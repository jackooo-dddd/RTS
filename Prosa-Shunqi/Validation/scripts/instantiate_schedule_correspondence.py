#!/usr/bin/env python3
"""Instantiate the audited Schedule correspondence DAG for an artifact.

The transformation changes only imported-artifact and certificate-module
names.  Generated files contain the original proof terms and are compiled by
Rocq for the exact imported artifact; this script introduces no assumption.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-dir", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--imported-module", required=True)
    parser.add_argument("--imported-artifact", required=True, type=Path)
    parser.add_argument("--target-prefix", required=True)
    parser.add_argument("--metadata", required=True, type=Path)
    parser.add_argument(
        "--module",
        action="append",
        choices=[
            "ScheduleFiniteOperations",
            "ScheduleCorrespondence",
            "ScheduleProcessorStateCorrespondence",
        ],
        help="Generate only this source module; repeat as needed",
    )
    args = parser.parse_args()

    if not args.imported_artifact.is_file():
        raise SystemExit("imported artifact is missing")

    modules = {
        "ScheduleFiniteOperations":
            f"{args.target_prefix}ScheduleFiniteOperations",
        "ScheduleCorrespondence":
            f"{args.target_prefix}ScheduleCorrespondence",
        "ScheduleProcessorStateCorrespondence":
            f"{args.target_prefix}ProcessorStateCorrespondence",
    }
    replacements = {
        "ImportedSchedule": args.imported_module,
        "ScheduleBaseAdapter": f"{args.target_prefix}ScheduleBaseAdapter",
        **modules,
    }
    selected = set(args.module or modules)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    generated: dict[str, dict[str, str]] = {}
    for source_name, output_name in modules.items():
        if source_name not in selected:
            continue
        source = args.source_dir / f"{source_name}.v"
        if not source.is_file():
            raise SystemExit(f"missing source certificate: {source}")
        text = source.read_text()
        for old, new in replacements.items():
            text = text.replace(old, new)
        header = (
            "(** GENERATED ARTIFACT-LOCAL INSTANTIATION.\n"
            f"    source: {source}\n"
            f"    source-sha256: {sha(source)}\n"
            f"    imported-artifact-sha256: {sha(args.imported_artifact)} *)\n"
        )
        output = args.output_dir / f"{output_name}.v"
        output.write_text(header + text)
        generated[output_name] = {
            "source": str(source),
            "source_sha256": sha(source),
            "output": str(output),
            "output_sha256": sha(output),
        }

    result = {
        "schema_version": 1,
        "method": "kernel_rechecked_artifact_local_module_instantiation",
        "imported_module": args.imported_module,
        "imported_artifact": str(args.imported_artifact),
        "imported_artifact_sha256": sha(args.imported_artifact),
        "generated": generated,
    }
    args.metadata.parent.mkdir(parents=True, exist_ok=True)
    args.metadata.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
