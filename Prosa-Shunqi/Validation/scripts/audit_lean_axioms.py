#!/usr/bin/env python3
"""Fail-closed classifier for Lean `#print axioms` output."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

LINE = re.compile(
    r"^'(.+)' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])$"
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if not args.log.is_file() or not args.log.stat().st_size:
        raise SystemExit("AUDIT_MISSING: Lean axiom log absent or empty")

    config = json.loads(args.config.read_text())
    expected = config["declarations"]
    found: dict[str, list[str]] = {}
    for line in args.log.read_text(errors="replace").splitlines():
        match = LINE.match(line.strip())
        if not match:
            continue
        name = match.group(1)
        if name in found:
            raise SystemExit(f"duplicate #print axioms result: {name}")
        found[name] = [] if match.group(2) is None else [
            item.strip() for item in match.group(2).split(",") if item.strip()
        ]

    missing = sorted(set(expected) - set(found))
    extra = sorted(set(found) - set(expected))
    report = {"audit_policy": "fail_closed", "missing": missing, "extra": extra,
              "declarations": {}}
    failed = bool(missing or extra)
    for name, spec in expected.items():
        actual = found.get(name)
        allowed = sorted(spec.get("allowed_axioms", []))
        unexpected = [] if actual is None else sorted(set(actual) - set(allowed))
        absent_allowed = [] if actual is None else sorted(set(allowed) - set(actual))
        status = "AUDIT_MISSING" if actual is None else (
            "FAILED_ASSUMPTION_AUDIT" if unexpected else "PASS"
        )
        if status != "PASS":
            failed = True
        report["declarations"][name] = {
            "status": status,
            "actual_axioms": actual,
            "allowed_axioms": allowed,
            "unexpected_axioms": unexpected,
            "allowed_but_unused": absent_allowed,
        }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
