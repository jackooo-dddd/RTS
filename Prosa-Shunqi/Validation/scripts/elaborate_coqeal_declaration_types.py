#!/usr/bin/env python3
"""Official-toolchain `Check @declaration` evidence for the 239 CoqEAL-boundary declarations.

The authoritative inventory (`planning/v06_dependency/`) marks every declaration of
`implementation/refinements/*` as `UNRESOLVED_EXTERNAL_BUILD_BOUNDARY_COQEAL`: the official
`prosa-0.6` switch (Rocq 9.0.1, MathComp 2.4.0) had no CoqEAL, so `elaborate_declaration_types.py`
could not elaborate them.  This script closes exactly that gap and nothing else:

* it does not modify `declaration_inventory.csv` or `declaration_type_evidence.json`; the evidence is
  written to the separate file `coqeal_declaration_type_evidence.json`;
* the probe is the original probe's preamble (all main modules, in the same order) followed by the
  14 refinements modules in layer order, then `Check @name` between the same BEGIN/END markers;
* it is run on the official `prosa-0.6` switch, on a copy of the pinned official source tree whose main
  package was built by `reproduce.sh`, with CoqEAL 2.1.2 built locally (unchanged) against that
  switch; normalization and hashing are those of `elaborate_declaration_types.py`;
* `merge` checks that every refinements source file still has its inventoried sha256, that each
  inventoried `source-command-sha256` row receives exactly one Check, and records the provenance.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from pathlib import Path


def normalize(text: str) -> str:
    return " ".join(text.split())


def sha_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    generate = sub.add_parser("generate")
    generate.add_argument("--inventory", type=Path, required=True)
    generate.add_argument("--files", type=Path, required=True)
    generate.add_argument("--output", type=Path, required=True)
    merge = sub.add_parser("merge")
    merge.add_argument("--inventory", type=Path, required=True)
    merge.add_argument("--files", type=Path, required=True)
    merge.add_argument("--source", type=Path, required=True)
    merge.add_argument("--probe-output", type=Path, required=True)
    merge.add_argument("--provenance", type=Path, required=True)
    merge.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args()

    declarations = list(csv.DictReader(args.inventory.open()))
    files = list(csv.DictReader(args.files.open()))
    ordered = sorted(files, key=lambda r: (int(r["layer"]), r["file"]))
    refinements = [row for row in declarations if "/refinements/" in row["source_file"]]

    if args.command == "generate":
        main_modules = [row["module"] for row in ordered if "/refinements/" not in row["file"]]
        ref_modules = [row["module"] for row in ordered if "/refinements/" in row["file"]]
        lines = ['Set Warnings "-notation-overridden".', "Set Printing Width 100000."]
        lines.extend(f"Require Import {module}." for module in main_modules + ref_modules)
        for row in refinements:
            name = row["qualified_name"]
            lines.extend([
                f'Goal True. idtac "BEGIN|{name}". Abort.',
                f"Check @{name}.",
                f'Goal True. idtac "END|{name}". Abort.',
            ])
        args.output.write_text("\n".join(lines) + "\n")
        print(json.dumps({"main_modules": len(main_modules), "refinements_modules": len(ref_modules),
                          "declarations": len(refinements)}))
        return

    for row in files:
        if "/refinements/" in row["file"]:
            got = sha_file(args.source / row["file"])
            if got != row["sha256"]:
                raise SystemExit(f"refinements source hash changed: {row['file']}")
    output = args.probe_output.read_text(errors="replace")
    if "Error" in output:
        raise SystemExit("probe output contains an error")
    pattern = re.compile(r"(?ms)^BEGIN\|([^\n]+)\n(.*?)^END\|\1\s*$")
    evidence: dict[str, dict[str, str]] = {}
    for match in pattern.finditer(output):
        name, rendered = match.group(1), match.group(2).strip()
        if name in evidence:
            raise SystemExit(f"duplicate Check block: {name}")
        normalized = normalize(rendered)
        evidence[name] = {
            "rendered_check": rendered,
            "normalized_check": normalized,
            "sha256": hashlib.sha256(normalized.encode()).hexdigest(),
        }
    for row in refinements:
        if row["type_evidence_status"] != "UNRESOLVED_EXTERNAL_BUILD_BOUNDARY_COQEAL":
            raise SystemExit(f"unexpected inventory status: {row['qualified_name']}")
        if not row["final_type_or_type_fingerprint"].startswith("source-command-sha256:"):
            raise SystemExit(f"unexpected inventory fingerprint: {row['qualified_name']}")
        item = evidence.get(row["qualified_name"])
        if item is None or not item["normalized_check"]:
            raise SystemExit(f"missing Check evidence: {row['qualified_name']}")
        item["inventory_fingerprint"] = row["final_type_or_type_fingerprint"]
        item["source_file"] = row["source_file"]
    if set(evidence) != {row["qualified_name"] for row in refinements}:
        raise SystemExit("probe output names differ from the inventory")
    payload = {
        "schema": "coqeal_declaration_type_evidence.v1",
        "provenance": json.loads(args.provenance.read_text()),
        "declarations": dict(sorted(evidence.items())),
    }
    args.evidence.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"expected": len(refinements), "captured": len(evidence)}))


if __name__ == "__main__":
    main()
