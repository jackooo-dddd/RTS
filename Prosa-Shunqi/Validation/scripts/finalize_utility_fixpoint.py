#!/usr/bin/env python3
"""Publish a fully audited, fresh util/fixpoint.v validation snapshot."""

import argparse
import csv
import hashlib
import json
import shutil
from datetime import datetime
from pathlib import Path


def sha(path: Path) -> str:
    if not path.is_file() or not path.stat().st_size:
        raise SystemExit(f"MISSING_OR_EMPTY:{path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--work", required=True, type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    validation = project / "Validation"
    work = args.work.resolve()
    pipeline = validation / "planning/v06_pipeline"
    logs = validation / "logs/translation_order/fixpoint"
    cluster_path = validation / "logs/translation_order/cluster_results/fixpoint.json"
    cluster = load(cluster_path)
    previous_path = pipeline / "util_int_module_status.json"
    previous = load(previous_path)
    prepared = load(work / "prepare_manifest.json")
    evidence = load(work / "prepare_run_evidence.json")
    build = load(work / "lean_source_build_manifest.json")
    assumptions = load(logs / "assumption_summary.json")["certificates"]
    lean_audit = load(logs / "lean_axiom_summary.json")
    baseline = load(logs / "baseline_after.json")
    source_metadata = load(work / "source/GeneratedFixpointSourceAll_extraction.json")
    inventory = [row for row in csv.DictReader(
        (validation / "planning/v06_dependency/declaration_inventory.csv").open())
        if row["source_file"] == "util/fixpoint.v"]
    names = [row["declaration_name"] for row in inventory]
    if len(names) != 17 or len(set(names)) != 17:
        raise SystemExit("SOURCE_INVENTORY_NOT_17_UNIQUE")
    rows = cluster.get("declarations", [])
    if (cluster.get("file_status") != "ACCEPTED_V06_FILE"
            or cluster.get("fresh_build") is not True
            or cluster.get("snapshot_id") != prepared.get("snapshot_id")
            or evidence.get("snapshot_id") != prepared.get("snapshot_id")
            or [row["rocq_declaration"].split(".")[-1] for row in rows] != names):
        raise SystemExit("CLUSTER_COVERAGE_OR_SNAPSHOT_MISMATCH")
    if (previous.get("status") != "PASS"
            or previous["coverage"]["accepted_files"] != 29
            or previous["coverage"]["accepted_declarations"] != 252
            or baseline.get("status") != "PASS"
            or build.get("status") != "PASS"
            or build.get("producer_mode") != "CLEAN_FULL"
            or source_metadata.get("source_commit") !=
               "414e66760333eaa4ef78c685bcf53291c527a548"):
        raise SystemExit("BASELINE_OR_FRESH_PROVENANCE_FAILED")
    if (len(assumptions) != 17 or len(lean_audit["declarations"]) != 17
            or lean_audit["missing"] or lean_audit["extra"]):
        raise SystemExit("AUDIT_COVERAGE_INCOMPLETE")
    for stage in evidence["stages"]:
        if stage["mode"] != "FRESH" or stage["executed"] is not True:
            raise SystemExit(f"STAGE_NOT_FRESH:{stage['stage']}")
        for relative, expected in stage["output_hashes"].items():
            if sha(work / relative) != expected:
                raise SystemExit(f"STAGE_ARTIFACT_CHANGED:{relative}")
    for relative, item in build["modules"].items():
        if (sha(work / "olean" / relative) != item["sha256"]
                or sha(project / item["source_path"]) != item["source_sha256"]):
            raise SystemExit(f"LEAN_DEPENDENCY_CHANGED:{relative}")
    for row in rows:
        name = row["rocq_declaration"].split(".")[-1]
        audit = assumptions[name]
        if (row["acceptance"] != "ACCEPTED_V06_TRANSLATION"
                or audit["status"] not in {
                    "CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
                or audit["semantic_premises"] or audit["unexpected"]
                or audit["statement_only_dependencies"]
                or audit["source_theorem_dependency"]
                or audit["target_theorem_dependency"]
                or lean_audit["declarations"][row["lean_declaration"]]["status"] != "PASS"
                or row["semantic_status"] != audit["status"]):
            raise SystemExit(f"DECLARATION_AUDIT_FAILED:{name}")
        if (row["fresh_olean_sha256"] != sha(work / "olean/Prosa/Util/Fixpoint.olean")
                or row["export_sha256"] != sha(work / "imported/Fixpoint.out")
                or row["imported_vo_sha256"] != sha(work / "imported/ImportedFixpoint.vo")):
            raise SystemExit(f"DECLARATION_ARTIFACT_CHANGED:{name}")

    destination = validation / "imported/translation_order/fixpoint"
    destination.mkdir(parents=True, exist_ok=True)
    publish_files = [
        (work / "imported/Fixpoint.out", destination / "Fixpoint.out"),
        (work / "imported/ImportedFixpoint.v", destination / "ImportedFixpoint.v"),
        (work / "imported/ImportedFixpoint.vo", destination / "ImportedFixpoint.vo"),
    ]
    for module in ["FixpointBaseCorrespondence", "FixpointMonotoneCorrespondence",
                   "FixpointTheoremCorrespondence", "FixpointMaxOperations",
                   "FixpointMaxTheoremCorrespondence", "FixpointAssumptionAudit"]:
        publish_files.append((work / "certificates" / f"{module}.vo",
                              destination / f"{module}.vo"))
    for source, target in publish_files:
        expected = sha(source)
        shutil.copy2(source, target)
        if sha(target) != expected:
            raise SystemExit(f"PUBLICATION_COPY_CORRUPT:{target}")
    published = {target.name: sha(target) for _, target in publish_files}
    accepted_count = sum(row["semantic_status"] == "CERTIFIED" for row in rows)
    foundation_count = len(rows) - accepted_count
    manifest = {
        "slice": "TRANSLATION_ORDER_UTIL_FIXPOINT",
        "generated_at": datetime.now().astimezone().isoformat(),
        "source_file": "util/fixpoint.v",
        "source_commit": cluster["source_commit"],
        "source_file_sha256": cluster["source_sha256"],
        "production_file": "Prosa/Util/Fixpoint.lean",
        "production_source_sha256": cluster["lean_source_sha256"],
        "production_olean_sha256": cluster["fresh_olean_sha256"],
        "export_sha256": cluster["export_sha256"],
        "import_sha256": cluster["imported_vo_sha256"],
        "source_acquisition_metadata_sha256": cluster["source_acquisition_metadata_sha256"],
        "cluster_evidence_sha256": sha(cluster_path),
        "lean_source_build_manifest_sha256": sha(work / "lean_source_build_manifest.json"),
        "prepare_manifest_sha256": sha(work / "prepare_manifest.json"),
        "prepare_evidence_sha256": sha(work / "prepare_run_evidence.json"),
        "assumption_summary_sha256": sha(logs / "assumption_summary.json"),
        "lean_axiom_summary_sha256": sha(logs / "lean_axiom_summary.json"),
        "baseline_audit_sha256": sha(logs / "baseline_after.json"),
        "published_artifact_hashes": published,
        "snapshot_id": prepared["snapshot_id"],
        "fresh_build": True,
        "declarations": rows,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = pipeline / "util_fixpoint_module_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    coverage = dict(previous["coverage"])
    coverage["accepted_files"] += 1
    coverage["accepted_declarations"] += 17
    status = {
        "slice": "TRANSLATION_ORDER_UTIL_FIXPOINT",
        "snapshot_id": prepared["snapshot_id"],
        "per_file": {"util/fixpoint.v": {
            "public_declarations": 17, "translated": 17, "proof_clean": 17,
            "certified": accepted_count,
            "certified_with_prop_sprop_foundation": foundation_count,
            "accepted": 17, "status": "ACCEPTED_V06_FILE"}},
        "coverage": coverage,
        "previous_status_sha256": sha(previous_path),
        "manifest_sha256": sha(manifest_path),
        "status": "PASS",
    }
    status_path = pipeline / "util_fixpoint_module_status.json"
    status_path.write_text(json.dumps(status, indent=2) + "\n")
    print(f"FIXPOINT_ACCEPTED:17;CERTIFIED:{accepted_count};"
          f"WITH_FOUNDATION:{foundation_count};"
          f"PROJECT:{coverage['accepted_declarations']}/2439")


if __name__ == "__main__":
    main()
