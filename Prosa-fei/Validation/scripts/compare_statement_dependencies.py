#!/usr/bin/env python3
"""Compare classified statement-only assumptions using machine-produced JSON."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


TARGETS = ("big_nat_eq0", "sum_of_ones", "sum_le_summation_range")


def dependencies(doc: dict, target: str) -> set[str]:
    return set(doc["certificates"][target]["statement_only_dependencies"])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--before", required=True, type=Path)
    parser.add_argument("--after", required=True, type=Path)
    parser.add_argument("--json", required=True, type=Path)
    parser.add_argument("--markdown", required=True, type=Path)
    args = parser.parse_args()

    before_doc = json.loads(args.before.read_text())
    after_doc = json.loads(args.after.read_text())
    result: dict[str, object] = {"targets": {}}
    lines = [
        "| Target | Before | After | Eliminated | Percentage |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for target in TARGETS:
        before = dependencies(before_doc, target)
        after = dependencies(after_doc, target)
        if not after <= before:
            raise SystemExit(f"{target}: after set contains new dependencies")
        eliminated = sorted(before - after)
        percentage = 100.0 * len(eliminated) / len(before) if before else 0.0
        result["targets"][target] = {
            "before": len(before),
            "after": len(after),
            "eliminated": len(eliminated),
            "remaining": len(after),
            "elimination_percentage": round(percentage, 2),
            "eliminated_dependencies": eliminated,
            "remaining_dependencies": sorted(after),
        }
        lines.append(
            f"| `{target}` | {len(before)} | {len(after)} | "
            f"{len(eliminated)} | {percentage:.2f}% |"
        )

    before_unique = set().union(*(dependencies(before_doc, t) for t in TARGETS))
    after_unique = set().union(*(dependencies(after_doc, t) for t in TARGETS))
    unique_eliminated = sorted(before_unique - after_unique)
    result["unique"] = {
        "before": len(before_unique),
        "after": len(after_unique),
        "eliminated": len(unique_eliminated),
        "remaining": len(after_unique),
        "elimination_percentage": round(
            100.0 * len(unique_eliminated) / len(before_unique), 2
        ) if before_unique else 0.0,
        "eliminated_dependencies": unique_eliminated,
        "remaining_dependencies": sorted(after_unique),
    }
    lines.extend([
        f"| **Unique union** | {len(before_unique)} | {len(after_unique)} | "
        f"{len(unique_eliminated)} | "
        f"{result['unique']['elimination_percentage']:.2f}% |",
        "",
        "Counts are derived from the two classifier JSON files, not hard-coded.",
    ])

    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    args.markdown.write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
