#!/usr/bin/env python3
"""Aggregate incremental utility clusters into the current batch truth."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


def main() -> None:
    validation = Path(__file__).resolve().parents[1]
    pipeline = validation / "planning/v06_pipeline"
    selection = json.loads(
        (pipeline / "utility_foundation_expansion_selection.json").read_text()
    )
    cluster_dir = validation / "logs/utility_foundation_expansion/cluster_results"
    clusters = [json.loads(path.read_text()) for path in sorted(cluster_dir.glob("*.json"))]
    progress_dir = validation / "logs/utility_foundation_expansion/progress_results"
    progress = [json.loads(path.read_text()) for path in sorted(progress_dir.glob("*.json"))]
    accepted_by_name = {
        row["rocq_declaration"]: row
        for cluster in clusters for row in cluster["declarations"]
    }
    progress_by_name = {
        row["rocq_declaration"]: row
        for result in progress for row in result["declarations"]
    }

    declarations = []
    for file_info in selection["selection"]["files"]:
        for selected in file_info["declarations"]:
            qname = selected["rocq_declaration"]
            if qname in accepted_by_name:
                declarations.append(accepted_by_name[qname])
            elif qname in progress_by_name:
                declarations.append(progress_by_name[qname])
            else:
                declarations.append({
                    "source_file": file_info["source_file"],
                    "rocq_declaration": qname,
                    "kind": selected["kind"],
                    "migration_action": selected["migration_action"],
                    "validation_class": selected["validation_class"],
                    "translation_status": "NOT_STARTED",
                    "semantic_status": "NOT_YET_VALIDATED",
                    "acceptance": "NOT_ACCEPTED",
                })

    file_rows = {}
    proof_clean_states = {
        "PROOF_CLEAN", "SEMANTIC_PROOF_COMPILED", "ACCEPTED"
    }
    for file_info in selection["selection"]["files"]:
        source_file = file_info["source_file"]
        rows = [row for row in declarations if row["source_file"] == source_file]
        translated = sum(row.get("lean_declaration") is not None for row in rows)
        accepted = sum(row["acceptance"] == "ACCEPTED_V06_TRANSLATION" for row in rows)
        proof_clean = sum(
            row["acceptance"] == "ACCEPTED_V06_TRANSLATION"
            or row.get("translation_status") in proof_clean_states
            for row in rows
        )
        semantic_compiled = sum(
            row["acceptance"] == "ACCEPTED_V06_TRANSLATION"
            or row.get("translation_status") == "SEMANTIC_PROOF_COMPILED"
            or row.get("semantic_status") == "SEMANTIC_PROOF_COMPILED"
            for row in rows
        )
        blocked_semantic = sum(
            row.get("semantic_status") == "BLOCKED_SEMANTIC_VALIDATION"
            for row in rows
        )
        if accepted == len(rows):
            workflow_status = "ACCEPTED_V06_FILE"
        elif blocked_semantic:
            workflow_status = "BLOCKED_SEMANTIC_VALIDATION"
        elif semantic_compiled:
            workflow_status = "SEMANTIC_PROOF_COMPILED"
        elif proof_clean:
            workflow_status = "PROOF_CLEAN"
        elif translated:
            workflow_status = "TRANSLATED"
        else:
            workflow_status = "NOT_STARTED"
        file_rows[source_file] = {
            "public_declarations": len(rows),
            "translated": translated,
            "proof_clean": proof_clean,
            "semantic_proof_compiled": semantic_compiled,
            "certified": accepted,
            "blocked_semantic_validation": blocked_semantic,
            "not_yet_validated": sum(
                row["semantic_status"] == "NOT_YET_VALIDATED" for row in rows
            ),
            "status": workflow_status,
            "acceptance_status": (
                "ACCEPTED_V06_FILE" if accepted == len(rows)
                else "PARTIAL_V06_FILE" if translated else "NOT_STARTED"
            ),
        }

    statuses = Counter(row["semantic_status"] for row in declarations)
    accepted_new = sum(
        row["acceptance"] == "ACCEPTED_V06_TRANSLATION" for row in declarations
    )
    translated_uncertified = sum(
        row.get("lean_declaration") is not None
        and row["acceptance"] != "ACCEPTED_V06_TRANSLATION"
        for row in declarations
    )
    accepted_files_new = sum(
        row["acceptance_status"] == "ACCEPTED_V06_FILE"
        for row in file_rows.values()
    )
    main_pass = accepted_new == 104

    manifest = {
        "slice": "UTILITY_FOUNDATION_EXPANSION",
        "freeze_policy": "Any source, type/body, tool, export/import, certificate, or assumption hash change invalidates its result.",
        "authority": selection["authority"],
        "selection_sha256": __import__("hashlib").sha256(
            (pipeline / "utility_foundation_expansion_selection.json").read_bytes()
        ).hexdigest(),
        "clusters": clusters,
        "progress_results": progress,
        "declarations": declarations,
    }
    (pipeline / "utility_foundation_expansion_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=False) + "\n"
    )

    attempted_files = sum(row["status"] != "NOT_STARTED" for row in file_rows.values())
    status = {
        "slice": "UTILITY_FOUNDATION_EXPANSION",
        "UTILITY_FOUNDATION_EXPANSION_STATUS": "PASS" if main_pass else "PARTIAL",
        "MAIN_104_STATUS": "PASS" if main_pass else "PARTIAL",
        "OPTIONAL_EXPANSION_STATUS": "NOT_STARTED",
        "files_attempted": attempted_files,
        "files_accepted": accepted_files_new,
        "files_partial": sum(
            row["acceptance_status"] == "PARTIAL_V06_FILE"
            for row in file_rows.values()
        ),
        "declarations_attempted": sum(
            row.get("lean_declaration") is not None for row in declarations
        ),
        "declarations_compiled": sum(
            row.get("lean_declaration") is not None for row in declarations
        ),
        "declarations_proof_clean": sum(
            row["acceptance"] == "ACCEPTED_V06_TRANSLATION"
            or row.get("translation_status") in proof_clean_states
            for row in declarations
        ),
        "declarations_SEMANTIC_PROOF_COMPILED": sum(
            row.get("translation_status") == "SEMANTIC_PROOF_COMPILED"
            or row.get("semantic_status") == "SEMANTIC_PROOF_COMPILED"
            for row in declarations
        ),
        "declarations_BLOCKED_SEMANTIC_VALIDATION": statuses[
            "BLOCKED_SEMANTIC_VALIDATION"
        ],
        "declarations_CERTIFIED": statuses["CERTIFIED"],
        "declarations_CERTIFIED_WITH_PROP_SPROP_FOUNDATION": statuses[
            "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
        ],
        "declarations_CONDITIONAL": statuses["CONDITIONAL"],
        "declarations_NOT_YET_VALIDATED": statuses["NOT_YET_VALIDATED"],
        "declarations_FAILED": sum(
            count for key, count in statuses.items() if key.startswith("FAILED")
        ),
        "per_file": file_rows,
        "coverage": {
            "accepted_files": 7 + accepted_files_new,
            "authoritative_files": 357,
            "accepted_declarations": 24 + accepted_new,
            "authoritative_declarations": 2439,
            "translated_but_not_certified": translated_uncertified,
            "deferred_external_boundary": 239,
        },
        "UTIL_ALL_READY": "NO",
        "READY_FOR_JOB_FOUNDATION": "NO",
    }
    (pipeline / "utility_foundation_expansion_status.json").write_text(
        json.dumps(status, indent=2, sort_keys=False) + "\n"
    )
    print(json.dumps(status, indent=2))


if __name__ == "__main__":
    main()
