#!/usr/bin/env python3
"""Conservative per-stage keys for Schedule/Service/Supply prepare artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def tree(path: Path, suffix: str) -> dict[str, str]:
    files = sorted(path.rglob("*"))
    result = {p.relative_to(path).as_posix(): sha(p)
              for p in files if p.is_file() and p.name.endswith(suffix)}
    if not result:
        raise SystemExit(f"empty stage input tree: {path}")
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", required=True,
                        choices=["lean_build", "source_acquisition", "export", "rocq_import"])
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--validation", required=True, type=Path)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--exporter", required=True, type=Path)
    parser.add_argument("--importer", required=True, type=Path)
    parser.add_argument("--prepared", required=True, type=Path)
    parser.add_argument("--function-hash", required=True)
    args = parser.parse_args()
    config = json.loads(args.config.read_text())
    roots = {name: value.resolve() for name, value in {
        "project": args.project, "validation": args.validation,
        "source": args.source, "exporter": args.exporter,
        "importer": args.importer,
    }.items()}
    inputs = {item["name"]: (roots[item["root"]] / item["path"]).resolve()
              for item in config["inputs"]}
    required: set[str] = set()
    if args.stage == "lean_build":
        required.update(name for name, path in inputs.items()
                        if path.suffix == ".lean" or name in {
                            "lean_toolchain", "lakefile", "lake_manifest",
                            "selection", "previous_status", "previous_manifest",
                        } or name.endswith("lean_axiom_config"))
        required.update(name for name in inputs if name.endswith("_interface"))
    elif args.stage == "source_acquisition":
        required.update(name for name in inputs if name.startswith("source_")
                        or name in {"declaration_inventory", "selection",
                                         "previous_status", "previous_manifest"})
    elif args.stage == "export":
        required.update(name for name in inputs if name.endswith("export_config")
                        or name == "lean4export")
    else:
        required.update(name for name in inputs if name.endswith("import_fixture")
                        or name.endswith("_export")
                        or name in {"rocq_import", "rocq_foundation"})
    if not required:
        raise SystemExit("no stage inputs declared")
    data = {
        "stage": args.stage,
        "function_hash": args.function_hash,
        "module_loading": config.get("module_loading", {}),
        "files": {},
        "fingerprint_implementation_sha256": sha(Path(__file__)),
    }
    for name in sorted(required):
        path = inputs[name]
        if not path.is_file() or not path.stat().st_size:
            raise SystemExit(f"missing stage input: {name}:{path}")
        data["files"][name] = sha(path)
    if args.stage == "lean_build":
        # A complete import closure is required: all production modules named
        # by the descriptor, then recursive direct Prosa imports. A missed
        # dependency fails before a cache lookup.
        visited: dict[str, str] = {}

        def visit(path: Path) -> None:
            path = path.resolve()
            if not path.is_file():
                raise SystemExit(f"missing imported production source: {path}")
            name = path.relative_to(args.project.resolve()).as_posix()
            if name in visited:
                return
            visited[name] = sha(path)
            for line in path.read_text().splitlines():
                line = line.split("--", 1)[0].strip()
                if line.startswith("import "):
                    for imported in line.split()[1:]:
                        if imported.startswith("Prosa."):
                            visit(args.project / (imported.replace(".", "/") + ".lean"))

        for name in sorted(required):
            if inputs[name].suffix == ".lean":
                visit(inputs[name])
        data["production_import_closure"] = visited
        data["mathlib_commit"] = subprocess.check_output(
            ["git", "-C", str(args.project / ".lake/packages/mathlib"),
             "rev-parse", "HEAD"], text=True).strip()
        data["lean_version"] = subprocess.check_output(
            ["lean", "--version"], text=True).strip()
        data["compiler_options"] = ["-DautoImplicit=false", "-R", str(args.project.resolve())]
        data["build_helpers"] = {
            p.name: sha(p) for p in [
                args.validation / "scripts/common/validation_common.sh",
                args.validation / "scripts/common/file_validate.sh",
                args.validation / "scripts/file_validate_lean_dependencies.py",
                args.validation / "scripts/audit_lean_axioms.py",
            ]
        }
    elif args.stage == "source_acquisition":
        data["source_commit"] = subprocess.check_output(
            ["git", "-C", str(args.source), "rev-parse", "HEAD"], text=True).strip()
        data["rocq_version"] = subprocess.check_output(
            ["opam", "exec", "--switch=rocq93rc1", "--", "rocq", "--version"],
            text=True).strip()
    elif args.stage == "export":
        data["built_olean"] = tree(args.prepared / "olean", ".olean")
        data["export_helper"] = sha(args.validation / "scripts/export_actual_artifact.sh")
    else:
        data["exported_out"] = tree(args.prepared / "imported", ".out")
        data["rocq_version"] = subprocess.check_output(
            ["opam", "exec", "--switch=rocq93rc1", "--", "rocq", "--version"],
            text=True).strip()
    print(hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest())


if __name__ == "__main__":
    main()
