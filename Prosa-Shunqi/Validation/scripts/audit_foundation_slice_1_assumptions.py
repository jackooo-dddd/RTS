#!/usr/bin/env python3
"""Fail-closed classifier for FOUNDATION_SLICE_1 Print Assumptions output."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


CERTIFICATES = [
    "rocq_nat_roundtrip",
    "imported_nat_roundtrip",
    "duration_relation_total_from_rocq",
    "duration_rocq_roundtrip_certificate",
    "duration_imported_roundtrip_certificate",
    "instant_relation_total_from_rocq",
    "instant_rocq_roundtrip_certificate",
    "instant_imported_roundtrip_certificate",
]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    if not args.log.is_file() or args.log.stat().st_size == 0:
        raise SystemExit("AUDIT_MISSING: assumption log absent or empty")
    text = args.log.read_text(errors="replace")
    event_pattern = re.compile(
        r"Closed under the global context"
        r"|Axioms:\s*\nLean\.eq relies on definitional UIP\."
    )
    events = event_pattern.findall(text)
    closed_count = sum(e.startswith("Closed") for e in events)
    importer_foundation_count = sum(e.startswith("Axioms") for e in events)
    unexplained = event_pattern.sub("", text).strip()
    forbidden = re.findall(
        r"(?im)^\s*(?:Axioms?|Assumptions?)\s*:|sorryAx|Admitted|\badmit\b",
        unexplained,
    )
    target_self_dependency = any(
        re.search(rf"(?m)^\s*{re.escape(name)}\s*:", text)
        for name in CERTIFICATES
    )
    complete = len(events) == len(CERTIFICATES) and not unexplained
    status = "CERTIFIED" if complete and not forbidden and not target_self_dependency else "FAILED_ASSUMPTION_AUDIT"
    per_certificate = {}
    if len(events) == len(CERTIFICATES):
        for name, event in zip(CERTIFICATES, events):
            per_certificate[name] = {
                "status": "CLOSED" if event.startswith("Closed") else "ALLOWED_IMPORTER_FOUNDATION",
                "assumptions": [] if event.startswith("Closed") else ["Lean.eq definitional UIP"],
            }
    result = {
        "audit_policy": "fail_closed",
        "expected_certificates": CERTIFICATES,
        "expected_print_count": len(CERTIFICATES),
        "closed_under_global_context_count": closed_count,
        "allowed_importer_foundation_count": importer_foundation_count,
        "allowed_importer_foundation": ["Lean.eq relies on definitional UIP"],
        "unparsed_or_truncated_output": unexplained,
        "unexpected_assumption_markers": forbidden,
        "target_certificate_self_dependency": target_self_dependency,
        "semantic_premises": [],
        "prop_sprop_foundation": [],
        "per_certificate": per_certificate,
        "status": status,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if status == "CERTIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
