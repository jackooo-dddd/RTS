#!/usr/bin/env python3
"""Instantiate the audited Euclidean div/mod bridge for one Lean artifact.

The proof source is the already accepted, kernel-checked prefix of
``DivModCorrespondence.v``.  Only module and lemma-name prefixes change; the
generated file is compiled and assumption-audited like handwritten Rocq.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


IDENT = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")
PREFIX = re.compile(r"^[a-z][a-z0-9_]*$")
END_MARKER = "\nLemma dm_div_floor_correspondence"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--proof-source", required=True, type=Path)
    parser.add_argument("--imported-module", required=True)
    parser.add_argument("--imported-artifact", required=True, type=Path)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--iff-mp-name", default="Iff_mp")
    parser.add_argument("--iff-mpr-name", default="Iff_mpr")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--metadata", required=True, type=Path)
    args = parser.parse_args()

    if not IDENT.fullmatch(args.imported_module):
        raise SystemExit("invalid imported module")
    if not PREFIX.fullmatch(args.prefix):
        raise SystemExit("invalid proof prefix")
    if not IDENT.fullmatch(args.iff_mp_name) or not IDENT.fullmatch(args.iff_mpr_name):
        raise SystemExit("invalid imported Iff projection name")
    for path in (args.proof_source, args.imported_artifact):
        if not path.is_file() or path.stat().st_size == 0:
            raise SystemExit(f"missing or empty input: {path}")

    source = args.proof_source.read_text()
    if source.count(END_MARKER) != 1:
        raise SystemExit("audited DivMod proof boundary changed")
    proof = source.split(END_MARKER, 1)[0]
    expected_import = (
        "From FoundationImported Require Import\n"
        "  ImportedDivMod ImportedNat ImportedSubadditivity."
    )
    replacement_import = (
        "From FoundationImported Require Import\n"
        f"  {args.imported_module} ImportedSubadditivity."
    )
    if proof.count(expected_import) != 1:
        raise SystemExit("audited DivMod import header changed")
    proof = proof.replace(expected_import, replacement_import)
    div_mod_only_definitions = """Definition dm_imported_div_floor (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.Prosa_Util_Div_mod_div_floor a b.

Definition dm_imported_div_ceil (a b : Lean.Nat) : Lean.Nat :=
  ImportedDivMod.Prosa_Util_Div_mod_div_ceil a b.

"""
    if proof.count(div_mod_only_definitions) != 1:
        raise SystemExit("audited DivMod-only definition block changed")
    proof = proof.replace(div_mod_only_definitions, "")
    proof = proof.replace("ImportedDivMod", args.imported_module)
    proof = proof.replace(
        f"{args.imported_module}.Iff_mpr", f"{args.imported_module}.{args.iff_mpr_name}"
    )
    proof = proof.replace(
        f"{args.imported_module}.Iff_mp", f"{args.imported_module}.{args.iff_mp_name}"
    )
    proof = proof.replace("dm_", f"{args.prefix}_")
    proof += "\n"
    if "ImportedDivMod" in proof:
        raise SystemExit("unsubstituted adapter token")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.metadata.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(proof)
    args.metadata.write_text(json.dumps({
        "schema_version": 1,
        "proof_source": str(args.proof_source.resolve()),
        "proof_source_sha256": sha(args.proof_source),
        "proof_boundary": END_MARKER.strip(),
        "imported_module": args.imported_module,
        "imported_artifact": str(args.imported_artifact.resolve()),
        "imported_artifact_sha256": sha(args.imported_artifact),
        "prefix": args.prefix,
        "iff_mp_name": args.iff_mp_name,
        "iff_mpr_name": args.iff_mpr_name,
        "output_sha256": sha(args.output),
        "proof_mode": "GENERATED_FROM_ACCEPTED_KERNEL_CHECKED_PROOF_SOURCE",
        "provided_operations": ["Nat.div", "Nat.mod", "Nat.dvd"],
        "semantic_assumptions_added": [],
    }, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
