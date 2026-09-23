#!/usr/bin/env python3
"""Seal and reuse an accepted Lean module closure for FILE_VALIDATE.

The producer must have been built with this script's source manifest. Older
build manifests do not prove that their transitive module sources are current.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path


OPTIONS = ["-DautoImplicit=false", "-R", "${PROJECT_ROOT}"]


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def git_head(path: Path) -> str:
    return subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
    ).strip()


def module_source(project: Path, relative: str) -> Path:
    if not relative.endswith(".olean"):
        raise ValueError(f"unexpected build output: {relative}")
    source = (project / relative.removesuffix(".olean")).with_suffix(".lean")
    if not source.is_file():
        raise ValueError(f"source missing for module: {relative}")
    return source


def imports(source: Path) -> list[str]:
    result = []
    for line in source.read_text().splitlines():
        line = line.split("--", 1)[0].strip()
        if line.startswith("import "):
            result.extend(name for name in line.split()[1:] if name.startswith("Prosa."))
    return sorted(set(result))


def environment(project: Path) -> dict:
    return {
        "lean_toolchain_sha256": sha(project / "lean-toolchain"),
        "lakefile_sha256": sha(project / "lakefile.lean"),
        "lake_manifest_sha256": sha(project / "lake-manifest.json"),
        "mathlib_commit": git_head(project / ".lake/packages/mathlib"),
        "lean_version": subprocess.check_output(["lean", "--version"], text=True).strip(),
        "compiler_options": OPTIONS,
        "project_root": str(project.resolve()),
        "module_loading": ["isolated_olean_first", "project_root", "pinned_lake_path"],
    }


def seal(args: argparse.Namespace) -> None:
    project, olean = args.project.resolve(), args.olean.resolve()
    files = sorted(olean.rglob("*.olean"))
    if not files:
        raise SystemExit("NO_FRESH_LEAN_MODULES")
    modules = {}
    for artifact in files:
        relative = artifact.relative_to(olean).as_posix()
        source = module_source(project, relative)
        modules[relative] = {
            "sha256": sha(artifact),
            "bytes": artifact.stat().st_size,
            "source_path": source.relative_to(project).as_posix(),
            "source_sha256": sha(source),
            "direct_prosa_imports": imports(source),
        }
    for relative, item in modules.items():
        for imported in item["direct_prosa_imports"]:
            imported_path = imported.replace(".", "/") + ".olean"
            if imported_path not in modules:
                raise SystemExit(f"INCOMPLETE_PROSA_IMPORT_CLOSURE:{relative}:{imported_path}")
    result = {
        "schema_version": 1,
        "status": "PASS",
        "producer_mode": args.mode,
        "module_count": len(modules),
        "environment": environment(project),
        "modules": modules,
    }
    if args.reuse_evidence:
        result["dependency_reuse"] = json.loads(args.reuse_evidence.read_text())
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


def fail(message: str, corrupt: bool = False) -> None:
    print(message, file=sys.stderr)
    raise SystemExit(3 if corrupt else 2)


def materialize(args: argparse.Namespace) -> None:
    project = args.project.resolve()
    producer = args.producer.resolve()
    try:
        build = json.loads((producer / "lean_source_build_manifest.json").read_text())
        prepared = json.loads((producer / "prepare_manifest.json").read_text())
        accepted = json.loads(args.accepted_manifest.read_text())
        status = json.loads(args.accepted_status.read_text())
    except (OSError, ValueError) as exc:
        fail(f"PRODUCER_EVIDENCE_MISSING_OR_INVALID:{exc}", corrupt=True)
    snapshot = prepared.get("snapshot_id")
    if (accepted.get("acceptance") != "ACCEPTED_V06_FILE"
            or accepted.get("snapshot_id") != snapshot
            or status.get("status") != "PASS"
            or build.get("status") != "PASS"):
        fail("PRODUCER_NOT_ACCEPTED_OR_SNAPSHOT_MISMATCH", corrupt=True)
    sealed = (prepared.get("outputs", {}).get("lean_build", {}).get("files", {}))
    build_path = producer / "lean_source_build_manifest.json"
    if sealed.get("lean_source_build_manifest.json") != sha(build_path):
        fail("PRODUCER_BUILD_MANIFEST_SEAL_MISMATCH", corrupt=True)
    if build.get("environment") != environment(project):
        fail("PRODUCER_ENVIRONMENT_STALE")
    modules = build.get("modules", {})
    if not modules or len(modules) != build.get("module_count"):
        fail("PRODUCER_MODULE_MANIFEST_CORRUPT", corrupt=True)
    production_file = accepted.get("production_file", "")
    if not production_file.startswith("Prosa/") or not production_file.endswith(".lean"):
        fail("PRODUCER_ACCEPTED_FILE_INVALID", corrupt=True)
    production_module = production_file.removesuffix(".lean") + ".olean"
    production = modules.get(production_module, {})
    if (production.get("sha256") != accepted.get("production_olean_sha256")
            or production.get("source_sha256") != accepted.get("production_source_sha256")
            or sealed.get("olean/" + production_module) != production.get("sha256")):
        fail("PRODUCER_ACCEPTED_ARTIFACT_MISMATCH", corrupt=True)
    required = {name.replace(".", "/") + ".olean" for name in args.module}
    if not required <= modules.keys():
        fail(f"PRODUCER_MISSING_MODULES:{sorted(required - modules.keys())}")
    # Every module in the producer closure is checked. This intentionally
    # over-invalidates when an unrelated producer module changes.
    for relative, item in modules.items():
        source = project / item["source_path"]
        if not source.is_file() or sha(source) != item["source_sha256"]:
            fail(f"PRODUCER_SOURCE_STALE:{relative}")
        artifact = producer / "olean" / relative
        if (not artifact.is_file() or artifact.stat().st_size != item["bytes"]
                or sha(artifact) != item["sha256"]):
            fail(f"PRODUCER_ARTIFACT_CORRUPT:{relative}", corrupt=True)
        if imports(source) != item["direct_prosa_imports"]:
            fail(f"PRODUCER_IMPORT_GRAPH_STALE:{relative}")
    closure: set[str] = set()

    def visit(relative: str) -> None:
        if relative in closure:
            return
        if relative not in modules:
            fail(f"PRODUCER_IMPORT_CLOSURE_MISSING:{relative}", corrupt=True)
        closure.add(relative)
        for imported in modules[relative]["direct_prosa_imports"]:
            visit(imported.replace(".", "/") + ".olean")

    for relative in sorted(required):
        visit(relative)
    destination = args.destination.resolve()
    copied = {}
    timings = []
    for relative in sorted(closure):
        started = time.monotonic_ns()
        source = producer / "olean" / relative
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_name(f".{target.name}.tmp.{os.getpid()}")
        shutil.copy2(source, temporary)
        if sha(temporary) != modules[relative]["sha256"]:
            temporary.unlink(missing_ok=True)
            fail(f"COPIED_ARTIFACT_CORRUPT:{relative}", corrupt=True)
        os.replace(temporary, target)
        copied[relative] = modules[relative]["sha256"]
        timings.append({
            "module": relative.removesuffix(".olean").replace("/", "."),
            "mode": "VERIFIED_CACHE", "execution_count": 0,
            "cache_hit_count": 1,
            "elapsed_seconds": round((time.monotonic_ns() - started) / 1e9, 6),
        })
    evidence = {
        "status": "PASS",
        "mode": "VERIFIED_CACHE",
        "producer_snapshot_id": snapshot,
        "producer_prepare_manifest_sha256": sha(producer / "prepare_manifest.json"),
        "producer_accepted_manifest_sha256": sha(args.accepted_manifest),
        "producer_accepted_status_sha256": sha(args.accepted_status),
        "producer_source_build_manifest_sha256": sha(producer / "lean_source_build_manifest.json"),
        "module_count": len(copied),
        "modules": copied,
        "module_timings": timings,
    }
    args.evidence.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    s = sub.add_parser("seal")
    s.add_argument("--project", required=True, type=Path)
    s.add_argument("--olean", required=True, type=Path)
    s.add_argument("--mode", required=True, choices=[
        "CLEAN_FULL", "FILE_VALIDATE", "FULL_FALLBACK"
    ])
    s.add_argument("--output", required=True, type=Path)
    s.add_argument("--reuse-evidence", type=Path)
    s.set_defaults(func=seal)
    m = sub.add_parser("materialize")
    m.add_argument("--project", required=True, type=Path)
    m.add_argument("--producer", required=True, type=Path)
    m.add_argument("--accepted-manifest", required=True, type=Path)
    m.add_argument("--accepted-status", required=True, type=Path)
    m.add_argument("--destination", required=True, type=Path)
    m.add_argument("--module", action="append", required=True)
    m.add_argument("--evidence", required=True, type=Path)
    m.set_defaults(func=materialize)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
