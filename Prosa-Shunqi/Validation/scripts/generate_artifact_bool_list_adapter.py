#!/usr/bin/env python3
"""Instantiate the audited Bool/eqType/seq adapter for one import artifact."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from string import Template


IDENT = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")
PREFIX = re.compile(r"^[a-z][a-z0-9_]*$")
PROVIDED_OPERATIONS = (
    "bool.roundtrip",
    "bool.truth",
    "eqtype.decidable_eq",
    "list.roundtrip",
    "list.membership",
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--template", required=True, type=Path)
    parser.add_argument("--imported-module", required=True)
    parser.add_argument("--imported-artifact", required=True, type=Path)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--capital-prefix", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--metadata", required=True, type=Path)
    parser.add_argument("--require-operation", action="append", default=[])
    args = parser.parse_args()
    for value, regex, label in (
        (args.imported_module, IDENT, "imported module"),
        (args.prefix, PREFIX, "prefix"),
        (args.capital_prefix, IDENT, "capital prefix"),
    ):
        if not regex.fullmatch(value):
            raise SystemExit(f"invalid {label}: {value}")
    if not args.imported_artifact.is_file() or args.imported_artifact.stat().st_size == 0:
        raise SystemExit(f"imported artifact missing: {args.imported_artifact}")
    missing = sorted(set(args.require_operation) - set(PROVIDED_OPERATIONS))
    if missing:
        for operation in missing:
            print(f"missing operation bridge: {operation}")
        raise SystemExit(2)
    template = Template(args.template.read_text())
    rendered = template.substitute(
        IMPORTED=args.imported_module,
        PREFIX=args.prefix,
        CAP=args.capital_prefix,
    )
    if "${" in rendered:
        raise SystemExit("unexpanded adapter template token")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.metadata.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered)
    result = {
        "schema_version": 1,
        "template_sha256": sha(args.template),
        "imported_module": args.imported_module,
        "imported_artifact": str(args.imported_artifact.resolve()),
        "imported_artifact_sha256": sha(args.imported_artifact),
        "prefix": args.prefix,
        "capital_prefix": args.capital_prefix,
        "output_sha256": sha(args.output),
        "proof_mode": "GENERATED_KERNEL_CHECKED_ROCQ_SOURCE",
        "provided_operations": list(PROVIDED_OPERATIONS),
        "requested_operations": sorted(set(args.require_operation)),
        "semantic_assumptions_added": [],
    }
    args.metadata.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
