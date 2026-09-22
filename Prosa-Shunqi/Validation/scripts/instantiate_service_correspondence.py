#!/usr/bin/env python3
"""Instantiate the audited Service certificate DAG for another Lean artifact.

This is a textual module adapter, not a proof assumption: it changes only the
imported artifact module and certificate file-module dependencies.  Every
generated proof is subsequently parsed and checked by Rocq's kernel, and the
metadata binds the exact source and imported-artifact hashes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--source-dir", required=True, type=Path)
    p.add_argument("--output-dir", required=True, type=Path)
    p.add_argument("--imported-module", required=True)
    p.add_argument("--imported-artifact", required=True, type=Path)
    p.add_argument("--metadata", required=True, type=Path)
    p.add_argument(
        "--target-prefix",
        default="Ready",
        help="Prefix for generated certificate modules (default: Ready)",
    )
    p.add_argument(
        "--module",
        action="append",
        choices=[
            "ServiceNatBoolOperations",
            "ServiceIntervalOperations",
            "ServiceScheduleOperations",
            "ServiceJobOperations",
            "ServiceCorrespondence",
        ],
        help="Generate only this source module; repeat as needed",
    )
    args = p.parse_args()
    if not args.imported_artifact.is_file():
        raise SystemExit("imported artifact is missing")

    modules = {
        name: name.replace("Service", args.target_prefix, 1)
        for name in [
            "ServiceNatBoolOperations",
            "ServiceIntervalOperations",
            "ServiceScheduleOperations",
            "ServiceJobOperations",
            "ServiceCorrespondence",
        ]
    }
    selected = set(args.module or modules)
    replacements = {
        "ImportedService": args.imported_module,
        "ServiceBaseAdapter": f"{args.target_prefix}BaseAdapter",
        **modules,
    }
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
