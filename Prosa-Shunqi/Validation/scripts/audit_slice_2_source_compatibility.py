#!/usr/bin/env python3
"""Fail-closed audit of the two Rocq-9.3 compatibility transformations.

The audit compares complete files, not selected snippets.  A validation copy
must equal the authoritative file after exactly the configured one-line
transformation.  Reversing that transformation must reproduce the
authoritative bytes and SHA-256.  Elaboration/type fidelity is checked
separately by the compiled source/type guards.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path


TRANSFORMS = {
    "util/tactics.v": (
        "Ltac done := solve [ ssreflect.done | eauto 4 with basic_rt_facts ].",
        "Ltac done := solve [ done | eauto 4 with basic_rt_facts ].",
        "Rocq-9.3 tactic-name compatibility; no public declaration command is changed",
    ),
    "util/seqset.v": (
        "  Definition set_of of phant T := set.",
        "  Definition set_of (_ : phant T) := set.",
        "Rocq-9.3 binder syntax compatibility; exact type is checked by a kernel guard",
    ),
}

TARGETS = {
    "util/tactics.v": ["neqP"],
    "util/rel.v": ["total_over_list", "antisymmetric_over_list"],
    "util/seqset.v": ["set", "set_of", "set_uniq"],
    "util/subadditivity.v": [
        "subadditive_at", "subadditive_until", "subadditive",
        "subadditive_standard", "subadditive_standard_equivalence",
        "subadditive_leq_mul",
    ],
    "util/supremum.v": [
        "supremum_unfold", "supremum_exists", "supremum_none",
        "supremum_in", "supremum_spec",
    ],
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--authoritative-root", required=True, type=Path)
    p.add_argument("--validation-root", required=True, type=Path)
    p.add_argument("--inventory", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    args = p.parse_args()

    inv = list(csv.DictReader(args.inventory.open()))
    by_key = {(r["source_file"], r["declaration_name"]): r for r in inv}
    files: dict[str, object] = {}
    failed: list[str] = []

    for rel, names in TARGETS.items():
        original = (args.authoritative_root / rel).read_bytes()
        validated = (args.validation_root / rel).read_bytes()
        entry: dict[str, object] = {
            "authoritative_sha256": sha(original),
            "validation_copy_sha256": sha(validated),
            "target_declarations": [],
        }
        if rel in TRANSFORMS:
            before, after, reason = TRANSFORMS[rel]
            original_text = original.decode()
            if original_text.count(before) != 1 or after in original_text:
                failed.append(f"{rel}: authoritative transform anchor is not unique")
                expected = b""
            else:
                expected = original_text.replace(before, after, 1).encode()
            if validated != expected:
                failed.append(f"{rel}: validation copy is not the exact approved transform")
            reversed_bytes = validated.decode().replace(after, before, 1).encode()
            if reversed_bytes != original:
                failed.append(f"{rel}: reverse normalization is not byte-identical")
            entry.update({
                "compatibility_transform": reason,
                "changed_lines": 1,
                "expected_transformed_sha256": sha(expected),
                "reverse_normalized_sha256": sha(reversed_bytes),
                "reverse_normalized_byte_identical": reversed_bytes == original,
            })
        else:
            if validated != original:
                failed.append(f"{rel}: unexpected source modification")
            entry.update({
                "compatibility_transform": None,
                "changed_lines": 0,
                "reverse_normalized_sha256": sha(validated),
                "reverse_normalized_byte_identical": validated == original,
            })
        for name in names:
            row = by_key.get((rel, name))
            if row is None:
                failed.append(f"{rel}:{name}: absent from pinned declaration inventory")
                continue
            entry["target_declarations"].append({
                "declaration": name,
                "qualified_name": row["qualified_name"],
                "source_command_sha256": row["source_command_sha256"],
                "elaborated_type_fingerprint": row["final_type_or_type_fingerprint"],
                "type_evidence_status": row["type_evidence_status"],
            })
        files[rel] = entry

    result = {
        "status": "PASS" if not failed else "FAIL_SOURCE_COMPATIBILITY_AUDIT",
        "policy": "complete-file exact transformation plus reverse byte identity; elaborated types checked by Rocq guards",
        "files": files,
        "failures": failed,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
