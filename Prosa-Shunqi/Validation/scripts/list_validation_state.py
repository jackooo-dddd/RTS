#!/usr/bin/env python3
"""Content-addressed state and timing for the bounded List validator.

This deliberately implements only the prepare/check/finalize workflow used by
the current List batch.  It is not a repository-wide cache framework.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def command(*args: str, cwd: Path | None = None) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def tree_files(root: Path, suffix: str) -> dict[str, str]:
    return {
        path.relative_to(root).as_posix(): sha(path)
        for path in sorted(root.rglob(f"*{suffix}"))
        if path.is_file()
    }


def require_file(path: Path) -> None:
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit(f"required input absent or empty: {path}")


def descriptor(args: argparse.Namespace) -> None:
    project = args.project_root.resolve()
    validation = args.validation_root.resolve()
    source = args.source_root.resolve()
    exporter = args.exporter_root.resolve()
    importer = args.importer_root.resolve()
    config = args.config.resolve()
    fixed_files = {
        "snapshot_config": config,
        "lean_toolchain": project / "lean-toolchain",
        "lakefile": project / "lakefile.lean",
        "lake_manifest": project / "lake-manifest.json",
        "computation_interface": validation
        / "fixtures/utility_foundation/ListLastComputationInterface.lean",
        "import_driver": validation
        / "fixtures/utility_foundation/ImportedListLast.v",
        "import_probe": validation
        / "fixtures/utility_foundation/ImportedListLastTypeProbe.v",
        "simple_import_driver": validation
        / "fixtures/utility_foundation/ImportedListSimple.v",
        "simple_import_probe": validation
        / "fixtures/utility_foundation/ImportedListSimpleTypeProbe.v",
        "source_extractor": validation / "scripts/extract_v06_semantic_source.py",
        "source_type_evidence": validation
        / "planning/v06_dependency/declaration_type_evidence.json",
        "tactics_patch": validation
        / "patches/prosa-v06-rocq93-util-tactics.patch",
        "accepted_subadditivity": validation
        / "imported/foundation_slice_2_closure/ImportedSubadditivity.vo",
        "official_list": source / "util/list.v",
        "official_tactics": source / "util/tactics.v",
        "official_supremum": source / "util/supremum.v",
        "lean4export_binary": exporter / ".lake/build/bin/lean4export",
        "rocq_import_plugin": importer / "src/lean_import.cmxs",
        "rocq_import_foundation": importer / "src/Lean.vo",
    }
    for path in fixed_files.values():
        require_file(path)
    inputs = {
        "schema_version": 1,
        "scope": "utility_list_current_batch",
        "files": {name: sha(path) for name, path in fixed_files.items()},
        # Conservative internal closure: the current workspace is still small,
        # and binding every production Lean source prevents undeclared imports
        # from escaping invalidation without pretending to have an exact DAG.
        "production_lean_tree": tree_files(project / "Prosa", ".lean"),
        "source_commit": command("git", "-C", str(source), "rev-parse", "HEAD"),
        "source_tree": command(
            "git", "-C", str(source), "rev-parse", "HEAD^{tree}"
        ),
        "mathlib_commit": command(
            "git", "-C", str(project / ".lake/packages/mathlib"),
            "rev-parse", "HEAD"
        ),
        "lean_version": command("lean", "--version"),
        "rocq_version": command(
            "opam", "exec", f"--switch={args.rocq_switch}", "--",
            "rocq", "--version"
        ),
        "module_loading": {
            "lean_root": str(project),
            "rocq_source_prefix": "prosa",
            "imported_prefix": "FoundationImported",
            "certificate_prefix": "FoundationCertificates",
            "autoImplicit": False,
            "export_module": (
                "Validation.fixtures.utility_foundation."
                "ListLastComputationInterface"
            ),
        },
    }
    result = {"snapshot_id": digest(inputs), "inputs": inputs}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(result["snapshot_id"])


def record(args: argparse.Namespace) -> None:
    entry = {
        "stage": args.stage,
        "mode": args.mode,
        "executed": args.executed == "true",
        "duration_seconds": round((args.end_ns - args.start_ns) / 1_000_000_000, 6),
        "start_ns": args.start_ns,
        "end_ns": args.end_ns,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("a") as stream:
        stream.write(json.dumps(entry, sort_keys=True) + "\n")


def load_events(path: Path) -> list[dict[str, object]]:
    if not path.is_file():
        return []
    return [json.loads(line) for line in path.read_text().splitlines() if line]


def finish_run(args: argparse.Namespace) -> None:
    events = []
    for path in args.events:
        events.extend(load_events(path))
    result = {
        "schema_version": 1,
        "snapshot_id": args.snapshot_id,
        "run_mode": args.run_mode,
        "recorded_at_unix_ns": time.time_ns(),
        "stages": events,
        "executed_stage_count": sum(bool(e["executed"]) for e in events),
        "verified_cache_hit_count": sum(
            e["mode"] == "VERIFIED_CACHE" for e in events
        ),
        "total_measured_seconds": round(
            sum(float(e["duration_seconds"]) for e in events), 6
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


def seal(args: argparse.Namespace) -> None:
    desc = json.loads(args.descriptor.read_text())
    config = json.loads(args.config.read_text())
    outputs: dict[str, dict[str, object]] = {}
    for stage, paths in config["prepared_outputs"].items():
        entries: dict[str, str] = {}
        for rel in paths:
            path = args.prepared / rel
            require_file(path)
            entries[rel] = sha(path)
        outputs[stage] = {"files": entries, "output_set_sha256": digest(entries)}
    result = {
        "schema_version": 1,
        "snapshot_id": desc["snapshot_id"],
        "descriptor_sha256": sha(args.descriptor),
        "input_descriptor": desc,
        "created_at_unix_ns": time.time_ns(),
        "outputs": outputs,
        "fresh_stage_evidence": load_events(args.events),
    }
    path = args.prepared / "prepare_manifest.json"
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(path)


def verify(args: argparse.Namespace) -> None:
    desc = json.loads(args.descriptor.read_text())
    manifest_path = args.prepared / "prepare_manifest.json"
    require_file(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("snapshot_id") != desc.get("snapshot_id"):
        raise SystemExit("PREPARED_SNAPSHOT_INPUT_MISMATCH")
    if manifest.get("input_descriptor") != desc:
        raise SystemExit("PREPARED_SNAPSHOT_DESCRIPTOR_MISMATCH")
    events: list[dict[str, object]] = []
    for stage, group in manifest.get("outputs", {}).items():
        started = time.time_ns()
        entries = group.get("files", {})
        if not entries or group.get("output_set_sha256") != digest(entries):
            raise SystemExit(f"PREPARED_ARTIFACT_MANIFEST_CORRUPT:{stage}")
        for rel, expected in entries.items():
            path = args.prepared / rel
            require_file(path)
            if sha(path) != expected:
                raise SystemExit(f"PREPARED_ARTIFACT_HASH_MISMATCH:{stage}:{rel}")
        ended = time.time_ns()
        events.append({
            "stage": stage,
            "mode": "VERIFIED_CACHE",
            "executed": False,
            "duration_seconds": round((ended - started) / 1_000_000_000, 6),
            "start_ns": started,
            "end_ns": ended,
        })
    result = {
        "schema_version": 1,
        "snapshot_id": desc["snapshot_id"],
        "run_mode": "INCREMENTAL",
        "recorded_at_unix_ns": time.time_ns(),
        "stages": events,
        "executed_stage_count": 0,
        "verified_cache_hit_count": len(events),
        "total_measured_seconds": round(
            sum(float(e["duration_seconds"]) for e in events), 6
        ),
    }
    args.run_evidence.parent.mkdir(parents=True, exist_ok=True)
    args.run_evidence.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.prepared)


def attach_publication(args: argparse.Namespace) -> None:
    """Bind a published cluster result to the completed finalize evidence."""
    result = json.loads(args.result.read_text())
    evidence = json.loads(args.evidence.read_text())
    if result.get("snapshot_id") != args.snapshot_id:
        raise SystemExit("PUBLICATION_RESULT_SNAPSHOT_MISMATCH")
    if evidence.get("snapshot_id") != args.snapshot_id:
        raise SystemExit("PUBLICATION_EVIDENCE_SNAPSHOT_MISMATCH")
    result["finalize_run_evidence"] = {
        "path": str(args.evidence.resolve()),
        "sha256": sha(args.evidence),
        "run_mode": evidence.get("run_mode"),
        "stage_modes": {
            stage["stage"]: stage["mode"]
            for stage in evidence.get("stages", [])
        },
    }
    args.result.write_text(json.dumps(result, indent=2, sort_keys=False) + "\n")


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="command", required=True)
    d = sub.add_parser("descriptor")
    d.add_argument("--project-root", required=True, type=Path)
    d.add_argument("--validation-root", required=True, type=Path)
    d.add_argument("--source-root", required=True, type=Path)
    d.add_argument("--exporter-root", required=True, type=Path)
    d.add_argument("--importer-root", required=True, type=Path)
    d.add_argument("--rocq-switch", required=True)
    d.add_argument("--config", required=True, type=Path)
    d.add_argument("--output", required=True, type=Path)
    d.set_defaults(func=descriptor)
    r = sub.add_parser("record")
    r.add_argument("--output", required=True, type=Path)
    r.add_argument("--stage", required=True)
    r.add_argument("--mode", required=True)
    r.add_argument("--executed", choices=("true", "false"), required=True)
    r.add_argument("--start-ns", type=int, required=True)
    r.add_argument("--end-ns", type=int, required=True)
    r.set_defaults(func=record)
    f = sub.add_parser("finish-run")
    f.add_argument("--events", type=Path, action="append", required=True)
    f.add_argument("--snapshot-id", required=True)
    f.add_argument("--run-mode", required=True)
    f.add_argument("--output", required=True, type=Path)
    f.set_defaults(func=finish_run)
    s = sub.add_parser("seal")
    s.add_argument("--descriptor", required=True, type=Path)
    s.add_argument("--config", required=True, type=Path)
    s.add_argument("--prepared", required=True, type=Path)
    s.add_argument("--events", required=True, type=Path)
    s.set_defaults(func=seal)
    v = sub.add_parser("verify")
    v.add_argument("--descriptor", required=True, type=Path)
    v.add_argument("--prepared", required=True, type=Path)
    v.add_argument("--run-evidence", required=True, type=Path)
    v.set_defaults(func=verify)
    a = sub.add_parser("attach-publication")
    a.add_argument("--result", required=True, type=Path)
    a.add_argument("--evidence", required=True, type=Path)
    a.add_argument("--snapshot-id", required=True)
    a.set_defaults(func=attach_publication)
    return p


if __name__ == "__main__":
    args = parser().parse_args()
    args.func(args)
