#!/usr/bin/env python3
"""Classify finite-sum dependency reduction from assumption-audit JSON files."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


TARGETS = ("big_nat_eq0", "sum_of_ones", "sum_le_summation_range")
REPRESENTATION = re.compile(
    r"Finset|Multiset|List_|__proof_|BitVec|AddMonoid_"
)


def deps(doc: dict, target: str) -> set[str]:
    return set(doc["certificates"][target]["statement_only_dependencies"])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--before", required=True, type=Path)
    parser.add_argument("--after", required=True, type=Path)
    parser.add_argument("--body-theorems", required=True, type=Path)
    parser.add_argument("--json", required=True, type=Path)
    parser.add_argument("--markdown", required=True, type=Path)
    args = parser.parse_args()
    before_doc = json.loads(args.before.read_text())
    after_doc = json.loads(args.after.read_text())
    body_names = {
        line.strip().replace(".", "_")
        for line in args.body_theorems.read_text().splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    }
    universe = sorted(set().union(*(deps(before_doc, t) for t in TARGETS)))
    rows = []
    for dependency in universe:
        short = dependency.rsplit(".", 1)[-1]
        initial = (
            "AVOID_BY_SEMANTIC_ABSTRACTION"
            if REPRESENTATION.search(short)
            else "DERIVE_FROM_SMALLER_LEMMAS"
        )
        outcomes = {}
        for target in TARGETS:
            if dependency in deps(after_doc, target):
                outcomes[target] = "D_STILL_REQUIRED"
            elif target in {"big_nat_eq0", "sum_of_ones"}:
                outcomes[target] = (
                    "C_SEMANTIC_ABSTRACTION" if REPRESENTATION.search(short)
                    else "B_NO_LONGER_NEEDED"
                )
            elif short in body_names:
                outcomes[target] = "B_IMPORTED_CHECKED_BODY_NOT_STATEMENT_AXIOM"
            else:
                outcomes[target] = "B_NO_LONGER_NEEDED"
        rows.append({
            "dependency": dependency,
            "initial_triage": initial,
            "replacement": (
                "Lean-defeq normalized List.range'/map/foldr target signature"
                if any(v.startswith(("B_", "C_")) for v in outcomes.values())
                else "none"
            ),
            "outcome_by_target": outcomes,
        })

    counts = {target: {"A": 0, "B": 0, "C": 0, "D": 0} for target in TARGETS}
    for row in rows:
        for target, outcome in row["outcome_by_target"].items():
            counts[target][outcome[0]] += 1
    output = {"counts": counts, "dependencies": rows}
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")

    lines = [
        "| Dependency | Initial triage | big_nat_eq0 | sum_of_ones | sum_le_summation_range |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        outcomes = row["outcome_by_target"]
        lines.append(
            f"| `{row['dependency']}` | {row['initial_triage']} | "
            f"{outcomes['big_nat_eq0']} | {outcomes['sum_of_ones']} | "
            f"{outcomes['sum_le_summation_range']} |"
        )
    lines.extend(["", "A = independently reproved in Rocq; B = no statement assumption needed; "
                  "C = avoided by semantic representation abstraction; D = still required."])
    args.markdown.write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
