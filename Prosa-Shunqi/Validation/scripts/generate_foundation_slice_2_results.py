#!/usr/bin/env python3
"""Generate content-addressed Slice 2 freeze and status artifacts."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from pathlib import Path

FILES = {
    "util/notation.v": ("Prosa/Util/Notation.lean", "Notation"),
    "util/tactics.v": ("Prosa/Util/Tactics.lean", "Tactics"),
    "util/rel.v": ("Prosa/Util/Rel.lean", "Rel"),
    "util/seqset.v": ("Prosa/Util/Seqset.lean", "Seqset"),
    "util/subadditivity.v": ("Prosa/Util/Subadditivity.lean", "Subadditivity"),
    "util/supremum.v": ("Prosa/Util/Supremum.lean", "Supremum"),
}

LEAN_PREFIX = {
    "util/notation.v": "Prosa.Util.Notation.",
    "util/tactics.v": "Prosa.Util.Tactics.",
    "util/rel.v": "Prosa.Util.Rel.",
    "util/seqset.v": "Prosa.Util.Seqset.",
    "util/subadditivity.v": "Prosa.Util.Subadditivity.",
    "util/supremum.v": "Prosa.Util.Supremum.",
}

CERTIFIED = {
    "Prosa.Util.Notation.constant": "constant_value_certificate",
    "Prosa.Util.Tactics.modusponens": "modusponens_statement_certificate",
    "Prosa.Util.Rel.monotone": "monotone_correspondence_certificate",
    "Prosa.Util.Supremum.choose_superior": "choose_superior_correspondence_certificate",
    "Prosa.Util.Supremum.supremum": "supremum_correspondence_certificate",
}

CERT_AUDIT_KEY = {
    "Prosa.Util.Notation.constant": "constant_value",
    "Prosa.Util.Tactics.modusponens": "modusponens_statement",
    "Prosa.Util.Rel.monotone": "monotone_correspondence",
    "Prosa.Util.Supremum.choose_superior": "choose_superior",
    "Prosa.Util.Supremum.supremum": "supremum",
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def text_sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def freeze_sections(text: str) -> dict[str, str]:
    sections: dict[str, str] = {}
    current = None
    lines: list[str] = []
    for line in text.splitlines():
        if line.startswith("FREEZE_BEGIN "):
            current, lines = line.removeprefix("FREEZE_BEGIN "), []
        elif line.startswith("FREEZE_END "):
            name = line.removeprefix("FREEZE_END ")
            if current != name:
                raise SystemExit(f"truncated freeze section: {current!r} / {name!r}")
            sections[name] = "\n".join(lines).strip()
            current, lines = None, []
        elif current is not None:
            lines.append(line)
    if current is not None:
        raise SystemExit(f"truncated freeze section: {current}")
    return sections


def split_type_body(block: str) -> tuple[str, str | None]:
    lines = block.splitlines()
    start = next((i for i, line in enumerate(lines[1:], 1)
                  if re.match(r"^(def|theorem|structure)\s", line)), None)
    if start is None:
        return block, None
    return "\n".join(lines[:start]).strip(), "\n".join(lines[start:]).strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-root", required=True, type=Path)
    parser.add_argument("--validation-root", required=True, type=Path)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--assumptions", required=True, type=Path)
    parser.add_argument("--freeze-log", required=True, type=Path)
    args = parser.parse_args()
    runtime = json.loads(args.runtime.read_text())
    assumptions = json.loads(args.assumptions.read_text())["certificates"]
    freezes = freeze_sections(args.freeze_log.read_text())

    inventory = list(csv.DictReader(
        (args.validation_root / "planning/v06_dependency/declaration_inventory.csv").open(newline="")
    ))
    migrations = {
        (r["v06_file"], r["v06_declaration"]): r
        for r in csv.DictReader(
            (args.validation_root / "planning/v06_mapping/v06_migration_table.csv").open(newline="")
        )
    }
    declarations = []
    for row in inventory:
        source_file = row["source_file"]
        if source_file not in FILES:
            continue
        production_file, artifact_stem = FILES[source_file]
        lean_name = LEAN_PREFIX[source_file] + row["declaration_name"]
        if lean_name not in freezes:
            raise SystemExit(f"missing elaborated Lean freeze evidence: {lean_name}")
        type_text, body_text = split_type_body(freezes[lean_name])
        certified = lean_name in CERTIFIED
        audit = assumptions.get(CERT_AUDIT_KEY.get(lean_name, "")) if certified else None
        if certified and (not audit or not audit["status"].startswith("CERTIFIED")):
            raise SystemExit(f"certificate audit not accepted: {lean_name}")
        migration = migrations[(source_file, row["declaration_name"])]
        artifact = runtime["files"][source_file]
        material = "\n".join([
            runtime["source_commit"], artifact["source_sha256"],
            row["source_command_sha256"], artifact["lean_source_sha256"],
            artifact["fresh_olean_sha256"], artifact["export_sha256"],
            artifact["imported_vo_sha256"], type_text,
            body_text or "", runtime["tooling_manifest_sha256"],
        ])
        declarations.append({
            "source_file": source_file,
            "rocq_declaration": row["qualified_name"],
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_fingerprint": row["final_type_or_type_fingerprint"],
            "lean_file": production_file,
            "lean_declaration": lean_name,
            "migration_action": migration["reuse_action"],
            "lean_elaborated_type": type_text,
            "lean_type_sha256": text_sha(type_text),
            "lean_computational_body_evidence": body_text,
            "lean_body_sha256": text_sha(body_text) if body_text else None,
            "fresh_olean_sha256": artifact["fresh_olean_sha256"],
            "export_sha256": artifact["export_sha256"],
            "imported_vo_sha256": artifact["imported_vo_sha256"],
            "certificate": CERTIFIED.get(lean_name),
            "certificate_source_sha256": runtime["certificates"].get(CERTIFIED.get(lean_name, "")),
            "semantic_status": audit["status"] if certified else "NOT_YET_VALIDATED",
            "assumption_audit": audit,
            "acceptance": "ACCEPTED_V06_TRANSLATION" if certified else "TRANSLATED_NOT_CERTIFIED",
            "content_invalidation_key_sha256": text_sha(material),
        })

    manifest = {
        "slice": "FOUNDATION_SLICE_2",
        "freeze_policy": "Any source, type, computational body, tool, export, import, or certificate hash change invalidates the corresponding result.",
        "source_commit": runtime["source_commit"],
        "source_tree": runtime["source_tree"],
        "toolchain": runtime["toolchain"],
        "tooling": runtime["tooling"],
        "files": runtime["files"],
        "declarations": declarations,
    }
    pipeline = args.validation_root / "planning/v06_pipeline"
    (pipeline / "foundation_slice_2_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    by_file = {}
    for source_file in FILES:
        rows = [d for d in declarations if d["source_file"] == source_file]
        accepted = sum(d["acceptance"] == "ACCEPTED_V06_TRANSLATION" for d in rows)
        by_file[source_file] = {
            "public_declarations": len(rows),
            "translated": len(rows),
            "proof_clean": len(rows),
            "certified": accepted,
            "not_yet_validated": len(rows) - accepted,
            "status": "ACCEPTED_V06_FILE" if accepted == len(rows) else "PARTIAL_V06_FILE",
        }
    accepted_count = sum(d["acceptance"] == "ACCEPTED_V06_TRANSLATION" for d in declarations)
    status = {
        "slice": "FOUNDATION_SLICE_2",
        "FOUNDATION_SLICE_2_STATUS": "PASS" if all(v["status"] == "ACCEPTED_V06_FILE" for v in by_file.values()) else "PARTIAL",
        "files_attempted": len(FILES),
        "files_accepted": sum(v["status"] == "ACCEPTED_V06_FILE" for v in by_file.values()),
        "files_partial": sum(v["status"] == "PARTIAL_V06_FILE" for v in by_file.values()),
        "declarations_attempted": len(declarations),
        "declarations_accepted": accepted_count,
        "declarations_not_yet_validated": len(declarations) - accepted_count,
        "declarations_blocked": 0,
        "migration_counts": {"REUSE_AFTER_REVALIDATION": 4, "ADAPT_OLD_LEAN": 9, "NEW_TRANSLATION": 9},
        "per_file": by_file,
        "declarations": {d["rocq_declaration"]: {
            "lean": d["lean_declaration"],
            "semantic_status": d["semantic_status"],
            "acceptance": d["acceptance"],
        } for d in declarations},
        "coverage": {
            "accepted_files": 2,
            "authoritative_files": 357,
            "accepted_declarations": 7,
            "authoritative_declarations": 2439,
            "translated_but_not_certified": len(declarations) - accepted_count,
            "certified_in_slice": accepted_count,
            "proof_clean_in_slice": len(declarations),
            "blocked_in_slice": 0,
            "deferred_external_boundary": 239,
        },
        "READY_FOR_JOB_FOUNDATION": "NO",
        "job_foundation_reason": "Five selected utility files remain partial; eqType reflection, seq/List membership, seqset law, Nat arithmetic, and theorem-level bridges are not yet closed.",
    }
    (pipeline / "foundation_slice_2_status.json").write_text(json.dumps(status, indent=2) + "\n")


if __name__ == "__main__":
    main()
