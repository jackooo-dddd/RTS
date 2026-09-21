#!/usr/bin/env python3
"""Fail closed if any of the previously accepted 24 declarations is invalidated."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree_hash(root: Path, suffixes: set[str] | None = None) -> str:
    h = hashlib.sha256()
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        if suffixes is not None and path.suffix not in suffixes:
            continue
        h.update(str(path.relative_to(root)).encode() + b"\0")
        h.update(path.read_bytes())
    return h.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    project = args.project_root.resolve()
    validation = project / "Validation"
    pipeline = validation / "planning/v06_pipeline"
    selection = json.loads(
        (pipeline / "utility_foundation_expansion_selection.json").read_text()
    )
    slice1 = json.loads((pipeline / "foundation_slice_1_manifest.json").read_text())
    slice2 = json.loads(
        (pipeline / "foundation_slice_2_closure_manifest.json").read_text()
    )

    expected_files = {
        "Prosa/Behavior/Time.lean": slice1["artifacts"]["lean_source_sha256"],
    }
    stems = {
        "util/notation.v": "Notation",
        "util/tactics.v": "Tactics",
        "util/rel.v": "Rel",
        "util/seqset.v": "Seqset",
        "util/subadditivity.v": "Subadditivity",
        "util/supremum.v": "Supremum",
    }
    for source_file, stem in stems.items():
        expected_files[f"Prosa/Util/{stem}.lean"] = (
            slice2["files"][source_file]["lean_source_sha256"]
        )

    mismatches = []
    actual_files = {}
    for relative, expected in expected_files.items():
        path = project / relative
        actual = sha(path) if path.is_file() else None
        actual_files[relative] = actual
        if actual != expected:
            mismatches.append({
                "field": relative,
                "expected": expected,
                "actual": actual,
            })

    checks = {
        "foundation_slice_2_closure_manifest_sha256": sha(
            pipeline / "foundation_slice_2_closure_manifest.json"
        ),
        "foundation_slice_2_closure_status_sha256": sha(
            pipeline / "foundation_slice_2_closure_status.json"
        ),
        "dependency_planning_tree_sha256": tree_hash(
            validation / "planning/v06_dependency"
        ),
        "mapping_planning_tree_sha256": tree_hash(
            validation / "planning/v06_mapping"
        ),
        "historical_production_lean_tree_sha256": tree_hash(
            project.parent / "Prosa-fei/Prosa", {".lean"}
        ),
        "accepted_production_files": actual_files,
    }
    expected_selection = selection["baseline"]
    for key in [
        "foundation_slice_2_closure_manifest_sha256",
        "foundation_slice_2_closure_status_sha256",
    ]:
        if checks[key] != expected_selection[key]:
            mismatches.append({
                "field": key,
                "expected": expected_selection[key],
                "actual": checks[key],
            })

    closure_baseline = slice2["baseline_freeze_check"]["checked"]
    for key in [
        "dependency_planning_tree_sha256",
        "mapping_planning_tree_sha256",
        "historical_production_lean_tree_sha256",
    ]:
        if checks[key] != closure_baseline[key]:
            mismatches.append({
                "field": key,
                "expected": closure_baseline[key],
                "actual": checks[key],
            })

    result = {
        "status": "PASS" if not mismatches else "INVALIDATE_EXISTING_CERTIFICATE",
        "frozen_accepted_declarations": 24,
        "checks": checks,
        "mismatches": mismatches,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
