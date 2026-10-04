#!/usr/bin/env python3
"""Official-toolchain `Check @declaration` evidence for source-`Local` lemmas (opt-in `local_declarations`).

The authoritative inventory (`planning/v06_dependency/declaration_inventory.csv`) lists the public declarations
of Prosa v0.6; a `Local Lemma` is not among them.  When a spec opts in to certifying such a lemma (user decision
2026-10-04: ProsaBuddy task `job_arrival_is_bounded` of `analysis/abstract/restricted_supply/bounded_bi/jlfp.v`),
this script records its elaborated type exactly as `elaborate_declaration_types.py` records the public ones:

* it does not modify `declaration_inventory.csv` or `declaration_type_evidence.json`; the rows and the evidence
  are written to the separate files `local_declaration_inventory.csv` and `local_declaration_type_evidence.json`;
* the probe is the original probe's preamble (all main modules, in the same order) followed by `Check @name`
  between the same BEGIN/END markers; it is run with `coqtop` on the official `prosa-0.6` switch on a build of
  the pinned official source tree; normalization and hashing are those of `elaborate_declaration_types.py`;
* `merge` checks that each source file still has its inventoried sha256, that the name is a unique source-`Local`
  lemma of that file and is absent from the authoritative inventory, and records the provenance.

usage:
  elaborate_local_declaration_types.py generate --files FILE_INVENTORY --declaration SOURCE_FILE:NAME ... --output PROBE.v
  elaborate_local_declaration_types.py merge --inventory INVENTORY --files FILE_INVENTORY --source PINNED_TREE
      --declaration SOURCE_FILE:NAME ... --probe-output STDOUT --provenance PROVENANCE.json
      --local-inventory OUT.csv --evidence OUT.json
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


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def qualified(source_file: str, name: str) -> str:
    return "prosa." + source_file[:-2].replace("/", ".") + "." + name


def parse_declarations(items: list[str]) -> list[tuple[str, str]]:
    out = []
    for item in items:
        source_file, sep, name = item.rpartition(":")
        if not sep or not source_file.endswith(".v") or not name:
            raise SystemExit(f"invalid --declaration {item!r} (expected SOURCE_FILE:NAME)")
        out.append((source_file, name))
    return out


LOCAL_RE = r"(?ms)^[ \t]*Local[ \t]+(Lemma|Theorem|Fact|Corollary|Remark|Proposition)\s+{name}(?![\w']).*?^[^\n]*(?:Qed|Defined)\.[ \t]*$"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    generate = sub.add_parser("generate")
    generate.add_argument("--files", type=Path, required=True)
    generate.add_argument("--declaration", action="append", required=True)
    generate.add_argument("--output", type=Path, required=True)
    merge = sub.add_parser("merge")
    merge.add_argument("--inventory", type=Path, required=True)
    merge.add_argument("--files", type=Path, required=True)
    merge.add_argument("--source", type=Path, required=True)
    merge.add_argument("--declaration", action="append", required=True)
    merge.add_argument("--probe-output", type=Path, required=True)
    merge.add_argument("--provenance", type=Path, required=True)
    merge.add_argument("--local-inventory", type=Path, required=True)
    merge.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args()
    wanted = parse_declarations(args.declaration)
    files = list(csv.DictReader(args.files.open()))

    if args.command == "generate":
        main_modules = [row["module"] for row in sorted(files, key=lambda r: (int(r["layer"]), r["file"]))
                        if "/refinements/" not in row["file"]]
        lines = ['Set Warnings "-notation-overridden".', "Set Printing Width 100000."]
        lines.extend(f"Require Import {module}." for module in main_modules)
        for source_file, name in wanted:
            q = qualified(source_file, name)
            lines.extend([f'Goal True. idtac "BEGIN|{q}". Abort.', f"Check @{q}.", f'Goal True. idtac "END|{q}". Abort.'])
        args.output.write_text("\n".join(lines) + "\n")
        print(json.dumps({"main_modules": len(main_modules), "declarations": len(wanted)}))
        return

    inventory = list(csv.DictReader(args.inventory.open()))
    fieldnames = list(inventory[0])
    file_sha = {row["file"]: row["sha256"] for row in files}
    output = args.probe_output.read_text(errors="replace")
    if "Error" in output:
        raise SystemExit("probe output contains an error")
    pattern = re.compile(r"(?ms)^BEGIN\|([^\n]+)\n(.*?)^END\|\1\s*$")
    checks: dict[str, str] = {}
    for match in pattern.finditer(output):
        if match.group(1) in checks:
            raise SystemExit(f"duplicate Check block: {match.group(1)}")
        checks[match.group(1)] = match.group(2).strip()
    rows, evidence = [], {}
    for source_file, name in wanted:
        q = qualified(source_file, name)
        text_bytes = (args.source / source_file).read_bytes()
        if sha_bytes(text_bytes) != file_sha.get(source_file):
            raise SystemExit(f"source hash changed: {source_file}")
        text = text_bytes.decode()
        found = list(re.finditer(LOCAL_RE.format(name=re.escape(name)), text))
        if len(found) != 1:
            raise SystemExit(f"not a unique source-local lemma: {source_file}:{name}")
        if any(r["qualified_name"] == q or (r["source_file"] == source_file and r["declaration_name"] == name)
               for r in inventory):
            raise SystemExit(f"already in the authoritative inventory: {q}")
        rendered = checks.get(q)
        if not rendered:
            raise SystemExit(f"missing Check evidence: {q}")
        normalized = normalize(rendered)
        digest = sha_bytes(normalized.encode())
        evidence[q] = {"rendered_check": rendered, "normalized_check": normalized, "sha256": digest,
                       "source_file": source_file, "source_kind": "Local " + found[0].group(1)}
        block = found[0].group(0).lstrip("\n")
        row = {k: "" for k in fieldnames}
        row.update(source_file=source_file, declaration_name=name, qualified_name=q, kind=found[0].group(1),
                   final_type_or_type_fingerprint="rocq-check-sha256:" + digest,
                   type_evidence_status="ELABORATED_ROCQ_CHECK", structure_fields_if_any="[]", attributes="local",
                   computational_body_mode="NO_INLINE_BODY", source_order="0",
                   source_line=str(text[:found[0].start()].count("\n") + 1 + (len(found[0].group(0)) -
                                                                              len(found[0].group(0).lstrip("\n")))),
                   source_command_sha256=sha_bytes(block.encode()))
        rows.append(row)
    if set(checks) != {qualified(s, n) for s, n in wanted}:
        raise SystemExit("probe output names differ from the requested declarations")
    with args.local_inventory.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader(); writer.writerows(rows)
    payload = {"schema": "local_declaration_type_evidence.v1",
               "provenance": json.loads(args.provenance.read_text()),
               "declarations": dict(sorted(evidence.items()))}
    args.evidence.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"declarations": len(rows)}))


if __name__ == "__main__":
    main()
