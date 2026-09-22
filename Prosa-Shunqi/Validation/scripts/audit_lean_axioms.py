#!/usr/bin/env python3
"""Fail-closed classifier for Lean `#print axioms` output."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

NO_AXIOMS_LINE = re.compile(r"^'(.+)' does not depend on any axioms$")
AXIOMS_START = re.compile(r"^'(.+)' depends on axioms: \[(.*)$")


def parse_axiom_results(text: str) -> dict[str, list[str]]:
    """Parse Lean's pretty-printed ``#print axioms`` results.

    Lean line-wraps a long axiom list according to the pretty-printer width.  A
    wrapped result is still one machine result, so collect continuation lines
    through the closing bracket.  Truncated or malformed records fail closed
    instead of being silently treated as missing output.
    """

    found: dict[str, list[str]] = {}
    pending_name: str | None = None
    pending_parts: list[str] = []

    def record(name: str, body: str) -> None:
        if name in found:
            raise SystemExit(f"duplicate #print axioms result: {name}")
        found[name] = [item.strip() for item in body.split(",") if item.strip()]

    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.strip()
        if pending_name is not None:
            if AXIOMS_START.match(line) or NO_AXIOMS_LINE.match(line):
                raise SystemExit(
                    "AUDIT_TRUNCATED: new #print axioms result before closing "
                    f"result for {pending_name} at line {line_number}"
                )
            if "]" in line:
                before, after = line.split("]", 1)
                if after.strip():
                    raise SystemExit(
                        "AUDIT_MALFORMED: trailing text after axiom list for "
                        f"{pending_name} at line {line_number}: {after.strip()}"
                    )
                pending_parts.append(before)
                record(pending_name, " ".join(pending_parts))
                pending_name = None
                pending_parts = []
            else:
                pending_parts.append(line)
            continue

        no_axioms = NO_AXIOMS_LINE.match(line)
        if no_axioms:
            record(no_axioms.group(1), "")
            continue

        axioms = AXIOMS_START.match(line)
        if not axioms:
            continue
        name, remainder = axioms.groups()
        if "]" in remainder:
            before, after = remainder.split("]", 1)
            if after.strip():
                raise SystemExit(
                    "AUDIT_MALFORMED: trailing text after axiom list for "
                    f"{name} at line {line_number}: {after.strip()}"
                )
            record(name, before)
        else:
            pending_name = name
            pending_parts = [remainder]

    if pending_name is not None:
        raise SystemExit(
            "AUDIT_TRUNCATED: missing closing bracket for #print axioms result "
            f"for {pending_name}"
        )
    return found


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
    found = parse_axiom_results(args.log.read_text(errors="replace"))

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
