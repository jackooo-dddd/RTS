#!/usr/bin/env python3
"""Classify per-certificate Rocq Print Assumptions output."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

import yaml


MARKER = re.compile(r"AUDIT_BEGIN\s+([A-Za-z0-9_]+)")
END_MARKER = re.compile(r"AUDIT_END\s+([A-Za-z0-9_]+)")
ASSUMPTION = re.compile(r"^([A-Za-z_][A-Za-z0-9_'.]*)\s+(?:relies\b|:)")


def sections(paths: list[Path]) -> tuple[dict[str, str], set[str]]:
    result: dict[str, str] = {}
    incomplete: set[str] = set()
    current: str | None = None
    chunks: list[str] = []
    for path in paths:
        for line in path.read_text().splitlines():
            match = MARKER.search(line)
            if match:
                if current is not None:
                    incomplete.add(current)
                    result[current] = "\n".join(chunks)
                current, chunks = match.group(1), []
            elif (match := END_MARKER.search(line)):
                if current == match.group(1):
                    result[current] = "\n".join(chunks)
                    current, chunks = None, []
                elif current is not None:
                    incomplete.add(current)
                    result[current] = "\n".join(chunks)
                    current, chunks = None, []
            elif current is not None:
                chunks.append(line)
        if current is not None:
            incomplete.add(current)
            result[current] = "\n".join(chunks)
            current, chunks = None, []
    return result, incomplete


def explicitly_allowed(name: str, allowed: set[str]) -> bool:
    return name in allowed or any(name.endswith("." + item) for item in allowed)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--log", action="append", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    config = yaml.safe_load(args.config.read_text())
    found, incomplete = sections(args.log)
    foundation = set(config["foundation_axioms"])
    statement_prefixes = tuple(config.get("statement_only_dependency_prefixes", []))
    importer_prefixes = tuple(config.get("importer_foundation_prefixes", []))
    allowed_importer = set(config.get("allowed_importer_assumptions", []))
    allow_legacy_prefixes = bool(config.get("allow_legacy_prefixes", True))
    require_end = bool(config.get("require_end_marker", False))
    report: dict[str, object] = {"certificates": {}}
    failed = False

    for key, spec in config["certificates"].items():
        text = found.get(key)
        if text is None or (require_end and key in incomplete):
            report["certificates"][key] = {
                "status": "AUDIT_MISSING",
                "reason": "missing or truncated Print Assumptions section"
            }
            failed = True
            continue
        entries = {m.group(1): line for line in text.splitlines()
                   if (m := ASSUMPTION.match(line))}
        names = sorted(entries)
        foundation_used = sorted(n for n in names
                                 if n in foundation or n.rsplit(".", 1)[-1] in foundation)
        statement_only = sorted(n for n in names
                                if n.rsplit(".", 1)[-1].startswith("Prosa_")
                                or (n.startswith(statement_prefixes)
                                    and "relies on definitional UIP" not in entries[n]))
        target = spec.get("target_imported_theorem")
        target_dependency = bool(target and any(
            n == target or n.endswith("." + target) for n in names))
        semantic = sorted(token for token in spec.get("semantic_premise_tokens", [])
                          if token in text)
        # Definitional UIP is an importer-declared representation principle.
        # Other imported primitives must match the explicit prefix allowlist.
        importer = sorted(n for n in names
                          if n not in foundation
                          and n.rsplit(".", 1)[-1] not in foundation
                          and n not in statement_only
                          and ("relies on definitional UIP" in entries[n]
                               or explicitly_allowed(n, allowed_importer)
                               or (allow_legacy_prefixes
                                   and n.startswith(importer_prefixes))))
        classified = set(foundation_used) | set(statement_only) | set(importer)
        unexpected = sorted(set(names) - classified)
        if target_dependency:
            unexpected.append(f"depends on target theorem {target}")
        if semantic:
            status = "CONDITIONAL"
        elif unexpected:
            status = "FAILED_ASSUMPTION_AUDIT"
            failed = True
        elif foundation_used and statement_only:
            status = "CERTIFIED_WITH_PROP_SPROP_FOUNDATION_AND_STATEMENT_EXPORT"
        elif foundation_used:
            status = "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
        elif statement_only:
            status = "CERTIFIED_WITH_STATEMENT_EXPORT_BOUNDARY"
        else:
            status = "CERTIFIED"
        report["certificates"][key] = {
            "certificate": spec["certificate"],
            "status": status,
            "foundation": foundation_used,
            "statement_only_dependencies": statement_only,
            "importer_foundation_or_primitives": importer,
            "semantic_premises": semantic,
            "target_theorem_dependency": target_dependency,
            "unexpected": unexpected,
        }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    for key, item in report["certificates"].items():
        print(f"{key:36} {item['status']}")
    if failed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
