#!/usr/bin/env python3
"""Non-gating export-size and per-target assumption inventory.

This reports evidence, not semantic acceptance. In particular an omitted Lean
proof body can remain an axiom in the imported Rocq artifact.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

from audit_assumptions import ENTRY, extract


NAME = re.compile(r"^(\d+) #N([SI]) (\d+) (\S+)$")
DECL = re.compile(r"^#(DEF|AX|IND|OPAQ) (.*)$")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inspect_export(path: Path) -> dict:
    names: dict[int, tuple[int, str]] = {0: (0, "")}
    raw_declarations: list[tuple[str, int]] = []
    line_count = 0
    with path.open(errors="replace") as stream:
        for line in stream:
            line_count += 1
            line = line.rstrip("\n")
            if match := NAME.match(line):
                index, kind, parent, suffix = match.groups()
                names[int(index)] = (int(parent), suffix if kind == "S" else suffix)
            elif match := DECL.match(line):
                kind, remainder = match.groups()
                fields = remainder.split()
                name_index = int(fields[1] if kind == "IND" else fields[0])
                raw_declarations.append((kind, name_index))

    resolved: dict[int, str] = {0: ""}

    def resolve(index: int) -> str:
        if index not in resolved:
            parent, suffix = names[index]
            prefix = resolve(parent)
            resolved[index] = prefix + ("." if prefix else "") + suffix
        return resolved[index]

    declarations = [(kind, resolve(index)) for kind, index in raw_declarations]
    return {
        "line_count": line_count,
        "byte_count": path.stat().st_size,
        "sha256": sha256(path),
        "serialized_declaration_count": len(declarations),
        "kind_counts": {
            kind: sum(actual == kind for actual, _ in declarations)
            for kind in ("DEF", "IND", "AX", "OPAQ")
        },
        "declarations": declarations,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--metadata", required=True, type=Path)
    parser.add_argument("--export", required=True, type=Path)
    parser.add_argument("--assumption-log", type=Path)
    parser.add_argument("--imported-namespace")
    parser.add_argument("--peer-export", type=Path)
    parser.add_argument("--stage-timings", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    for name in ("config", "metadata", "export"):
        path = getattr(args, name)
        if not path.is_file() or path.stat().st_size == 0:
            raise SystemExit(f"missing or empty {name}: {path}")
    config = json.loads(args.config.read_text())
    metadata = json.loads(args.metadata.read_text())
    if metadata.get("config_sha256") != sha256(args.config):
        raise SystemExit("export config hash does not match metadata")
    if metadata.get("output_sha256") != sha256(args.export):
        raise SystemExit("export artifact hash does not match metadata")
    if metadata.get("module") != config.get("module"):
        raise SystemExit("module identity does not match export metadata")

    exported = inspect_export(args.export)
    explicit_roots = set(config["targets"])
    present = {name for _, name in exported["declarations"]}
    missing_roots = sorted(explicit_roots - present)
    if missing_roots:
        raise SystemExit(f"export roots missing from artifact: {missing_roots}")
    names = [name for _, name in exported["declarations"]]
    if len(names) != len(set(names)):
        raise SystemExit("duplicate serialized declaration names")
    statement_only_names = {
        name for kind, name in exported["declarations"] if kind == "AX"
    }

    target_assumptions = None
    if args.assumption_log is not None:
        if not args.imported_namespace:
            raise SystemExit("--imported-namespace required with assumption log")
        if not args.assumption_log.is_file() or not args.assumption_log.stat().st_size:
            raise SystemExit("missing or empty marked assumption log")
        sections, incomplete = extract(args.assumption_log.read_text(errors="replace"))
        if incomplete or not sections:
            raise SystemExit(f"incomplete marked assumption sections: {sorted(incomplete)}")
        encoded_axioms = {
            name: re.compile(
                r"^" + re.escape(args.imported_namespace + "." + name.replace(".", "_"))
                + r"(?:_inst\d+)?$"
            ) for name in statement_only_names
        }
        target_assumptions = {}
        for target, section in sections.items():
            names_in_section = sorted(
                match.group(1) for line in section.splitlines()
                if (match := ENTRY.match(line))
            )
            mapped = {}
            unresolved_imported = []
            for entry in names_in_section:
                matches = [lean_name for lean_name, pattern in encoded_axioms.items()
                           if pattern.match(entry)]
                if len(matches) == 1:
                    mapped[entry] = matches[0]
                elif entry.startswith(args.imported_namespace + "."):
                    unresolved_imported.append(entry)
            target_assumptions[target] = {
                "imported_statement_only": sorted(mapped),
                "lean_statement_only_names": sorted(set(mapped.values())),
                "unresolved_imported_assumptions": sorted(set(unresolved_imported)),
                "other_assumptions": sorted(set(names_in_section) - set(mapped)
                                            - set(unresolved_imported)),
            }

    peer = None
    if args.peer_export is not None:
        if not args.peer_export.is_file() or not args.peer_export.stat().st_size:
            raise SystemExit("missing or empty peer export")
        peer = inspect_export(args.peer_export)
    timings = "NOT_RECORDED"
    if args.stage_timings is not None:
        if not args.stage_timings.is_file() or not args.stage_timings.stat().st_size:
            raise SystemExit("missing or empty stage timings")
        timings = json.loads(args.stage_timings.read_text())
    lines = exported["line_count"]
    diagnostics = [
        reason for needed, reason in (
            (lines > 100_000, "over_100k_lines"),
            (peer is not None and lines > 2 * peer["line_count"], "over_2x_peer"),
        ) if needed
    ]
    result = {
        "schema_version": 1,
        "purpose": "soft_dependency_budget_not_acceptance",
        "module": config["module"],
        "explicit_export_roots": sorted(explicit_roots),
        "explicit_export_root_count": len(explicit_roots),
        "serialized_declaration_count": exported["serialized_declaration_count"],
        "serialized_non_root_declaration_count": len(present - explicit_roots),
        "serialized_kind_counts": exported["kind_counts"],
        "export_line_count": lines,
        "export_byte_count": exported["byte_count"],
        "export_sha256": exported["sha256"],
        "statement_only_serialized_count": len(statement_only_names),
        "statement_only_serialized_names": sorted(statement_only_names),
        "per_target_assumptions": target_assumptions,
        "stage_timings": timings,
        "peer": None if peer is None else {
            "lines": peer["line_count"], "bytes": peer["byte_count"],
            "sha256": peer["sha256"],
        },
        "warning_over_50k_lines": lines > 50_000,
        "targeted_diagnostics_reasons": diagnostics,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "lines": lines, "bytes": exported["byte_count"],
        "roots": len(explicit_roots), "serialized_declarations": len(present),
        "non_roots": len(present - explicit_roots),
        "statement_only": len(statement_only_names),
        "warning": result["warning_over_50k_lines"],
        "diagnostics": diagnostics,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
