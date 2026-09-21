#!/usr/bin/env python3
"""Configuration-driven, fail-closed Print Assumptions classifier."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

BEGIN = re.compile(r"AUDIT_BEGIN\s+([A-Za-z0-9_.'-]+)")
END = re.compile(r"AUDIT_END\s+([A-Za-z0-9_.'-]+)")
ENTRY = re.compile(r"^([A-Za-z_][A-Za-z0-9_'.]*)\s+(?:relies\b|:)")


def extract(log: str) -> tuple[dict[str, str], set[str]]:
    result: dict[str, str] = {}
    incomplete: set[str] = set()
    current: str | None = None
    lines: list[str] = []
    for line in log.splitlines():
        if match := BEGIN.search(line):
            if current is not None:
                incomplete.add(current)
            current, lines = match.group(1), []
        elif match := END.search(line):
            if current == match.group(1):
                result[current] = "\n".join(lines)
            elif current is not None:
                incomplete.add(current)
            current, lines = None, []
        elif current is not None:
            lines.append(line)
    if current is not None:
        incomplete.add(current)
    return result, incomplete


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if not args.log.is_file() or not args.log.stat().st_size:
        raise SystemExit("AUDIT_MISSING: assumption log absent or empty")
    config = json.loads(args.config.read_text())
    found, incomplete = extract(args.log.read_text(errors="replace"))
    allowed_foundation = set(config.get("prop_sprop_foundation", []))
    allowed_importer = set(config.get("importer_foundation", []))
    allowed_rocq_sprop_uip = set(config.get("rocq_sprop_uip", []))
    report = {"audit_policy": "fail_closed", "certificates": {}}
    failed = False
    for key, spec in config["certificates"].items():
        text = found.get(key)
        if text is None or key in incomplete:
            report["certificates"][key] = {
                "status": "AUDIT_MISSING",
                "reason": "missing or truncated marked Print Assumptions section",
            }
            failed = True
            continue
        entries = {m.group(1): line for line in text.splitlines() if (m := ENTRY.match(line))}
        closed = "Closed under the global context" in text and not entries
        foundation = sorted(n for n in entries if n in allowed_foundation or n.rsplit(".", 1)[-1] in allowed_foundation)
        importer = sorted(n for n in entries if n in allowed_importer)
        rocq_sprop_uip = sorted(
            n for n, line in entries.items()
            if n in allowed_rocq_sprop_uip and "relies on definitional UIP" in line
        )
        target = spec.get("target_imported_theorem")
        target_dependency = bool(target and any(n == target or n.endswith("." + target) for n in entries))
        source = spec.get("source_theorem")
        source_dependency = bool(source and any(n == source or n.endswith("." + source) for n in entries))
        semantic = sorted(token for token in spec.get("semantic_premise_tokens", []) if token in text)
        classified = set(foundation) | set(importer) | set(rocq_sprop_uip)
        unexpected = sorted(set(entries) - classified)
        if target_dependency:
            unexpected.append(f"target theorem dependency: {target}")
        if source_dependency:
            unexpected.append(f"source theorem dependency: {source}")
        if semantic:
            status = "CONDITIONAL"
        elif unexpected:
            status = "FAILED_ASSUMPTION_AUDIT"
            failed = True
        elif foundation:
            status = "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
        elif closed or importer or rocq_sprop_uip:
            status = "CERTIFIED"
        else:
            status = "AUDIT_MISSING"
            failed = True
        report["certificates"][key] = {
            "certificate": spec["certificate"],
            "status": status,
            "closed": closed,
            "semantic_premises": semantic,
            "prop_sprop_foundation": foundation,
            "importer_foundation": importer,
            "rocq_sprop_definitional_uip": rocq_sprop_uip,
            "unexpected": unexpected,
            "target_theorem_dependency": target_dependency,
            "source_theorem_dependency": source_dependency,
            "raw_section_sha256": __import__("hashlib").sha256(text.encode()).hexdigest(),
        }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
