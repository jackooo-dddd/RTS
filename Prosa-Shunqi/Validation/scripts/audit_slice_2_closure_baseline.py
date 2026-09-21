#!/usr/bin/env python3
"""Capture/verify that closure work did not alter frozen production inputs."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


BASE_ACCEPTED = {
    "prosa.util.notation.constant",
    "prosa.util.tactics.modusponens",
    "prosa.util.rel.monotone",
    "prosa.util.supremum.choose_superior",
    "prosa.util.supremum.supremum",
}
FREEZE_FIELDS = [
    "source_command_sha256", "lean_type_sha256", "lean_body_sha256",
    "certificate_source_sha256",
]


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


def snapshot(project: Path) -> dict[str, object]:
    validation = project / "Validation"
    pipeline = validation / "planning/v06_pipeline"
    fs1 = json.loads((pipeline / "foundation_slice_1_manifest.json").read_text())
    fs2 = json.loads((pipeline / "foundation_slice_2_manifest.json").read_text())
    rows = {r["rocq_declaration"]: r for r in fs2["declarations"]}
    accepted = {}
    for name in sorted(BASE_ACCEPTED):
        row = rows[name]
        accepted[name] = {field: row.get(field) for field in FREEZE_FIELDS}
    return {
        "production_lean_tree_sha256": tree_hash(project / "Prosa", {".lean"}),
        "historical_production_lean_tree_sha256": tree_hash(project.parent / "Prosa-fei/Prosa", {".lean"}),
        "dependency_planning_tree_sha256": tree_hash(validation / "planning/v06_dependency"),
        "mapping_planning_tree_sha256": tree_hash(validation / "planning/v06_mapping"),
        "slice1_manifest_sha256": sha(pipeline / "foundation_slice_1_manifest.json"),
        "slice1_time_source_sha256": sha(project / "Prosa/Behavior/Time.lean"),
        "slice1_recorded_time_source_sha256": fs1["artifacts"]["lean_source_sha256"],
        "slice2_previously_accepted_freeze_fields": accepted,
    }


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("mode", choices=["capture", "verify"])
    p.add_argument("--project-root", required=True, type=Path)
    p.add_argument("--snapshot", required=True, type=Path)
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    now = snapshot(args.project_root)
    if args.mode == "capture":
        args.snapshot.parent.mkdir(parents=True, exist_ok=True)
        args.snapshot.write_text(json.dumps(now, indent=2, sort_keys=True) + "\n")
        print(json.dumps(now, indent=2, sort_keys=True))
        return 0

    before = json.loads(args.snapshot.read_text())
    mismatches = []
    for key in [
        "production_lean_tree_sha256",
        "historical_production_lean_tree_sha256",
        "dependency_planning_tree_sha256",
        "mapping_planning_tree_sha256",
        "slice1_manifest_sha256",
        "slice1_time_source_sha256",
    ]:
        if before[key] != now[key]:
            mismatches.append({"field": key, "before": before[key], "after": now[key]})
    if now["slice1_time_source_sha256"] != now["slice1_recorded_time_source_sha256"]:
        mismatches.append({
            "field": "slice1_time_source_vs_manifest",
            "actual": now["slice1_time_source_sha256"],
            "recorded": now["slice1_recorded_time_source_sha256"],
        })
    if (before["slice2_previously_accepted_freeze_fields"] !=
            now["slice2_previously_accepted_freeze_fields"]):
        mismatches.append({
            "field": "slice2_previously_accepted_freeze_fields",
            "before": before["slice2_previously_accepted_freeze_fields"],
            "after": now["slice2_previously_accepted_freeze_fields"],
        })
    result = {
        "status": "PASS" if not mismatches else "INVALIDATE_EXISTING_CERTIFICATE",
        "checked": now,
        "mismatches": mismatches,
    }
    output = args.output or args.snapshot.with_name("baseline_check.json")
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if mismatches else 0


if __name__ == "__main__":
    raise SystemExit(main())
