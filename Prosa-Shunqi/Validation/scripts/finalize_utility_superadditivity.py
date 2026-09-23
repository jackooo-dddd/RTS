#!/usr/bin/env python3
"""Fail-closed whole-file publication for pinned util/superadditivity.v."""

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
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    project, work = args.project.resolve(), args.work.resolve()
    validation = project / "Validation"
    pipeline = validation / "planning/v06_pipeline"
    cluster_path = validation / "logs/translation_order/cluster_results/superadditivity.json"
    previous_path = pipeline / "util_fixpoint_module_status.json"
    cluster, previous = load(cluster_path), load(previous_path)
    prepared = load(work / "prepare_manifest.json")
    evidence = load(work / "prepare_run_evidence.json")
    build = load(work / "lean_source_build_manifest.json")
    assumptions = load(work / "superadditivity_assumption_summary.json")["certificates"]
    lean_audit = load(work / "superadditivity_lean_axiom_summary.json")
    baseline = load(work / "superadditivity_baseline_audit.json")
    source_metadata = load(work / "source/OfficialSuperadditivityAll_extraction.json")
    inventory = [row for row in csv.DictReader(
        (validation / "planning/v06_dependency/declaration_inventory.csv").open())
        if row["source_file"] == "util/superadditivity.v"]
    names = [row["declaration_name"] for row in inventory]
    rows = cluster.get("declarations", [])
    if (len(names) != 12 or len(set(names)) != 12
            or cluster.get("file_status") != "ACCEPTED_V06_FILE"
            or cluster.get("fresh_build") is not True
            or cluster.get("snapshot_id") != prepared.get("snapshot_id")
            or evidence.get("snapshot_id") != prepared.get("snapshot_id")
            or [row["rocq_declaration"].split(".")[-1] for row in rows] != names):
        raise SystemExit("WHOLE_FILE_COVERAGE_OR_SNAPSHOT_MISMATCH")
    if (previous.get("status") != "PASS"
            or previous["coverage"]["accepted_files"] != 30
            or previous["coverage"]["accepted_declarations"] != 269
            or baseline.get("status") != "PASS"
            or build.get("status") != "PASS"
            or build.get("producer_mode") != "CLEAN_FULL"
            or source_metadata.get("source_commit") !=
               "414e66760333eaa4ef78c685bcf53291c527a548"
            or set(source_metadata["declarations"]) != set(names)):
        raise SystemExit("BASELINE_SOURCE_OR_FRESH_PROVENANCE_FAILED")
    if (len(assumptions) != 12 or len(lean_audit["declarations"]) != 12
            or lean_audit["missing"] or lean_audit["extra"]):
        raise SystemExit("AUDIT_COVERAGE_INCOMPLETE")
    for stage in evidence["stages"]:
        if stage["mode"] != "FRESH" or stage["executed"] is not True:
            raise SystemExit(f"STAGE_NOT_FRESH:{stage['stage']}")
        for relative, expected in stage["output_hashes"].items():
            if sha(work / relative) != expected:
                raise SystemExit(f"PREPARE_ARTIFACT_CHANGED:{relative}")
    for relative, item in build["modules"].items():
        if (sha(work / "olean" / relative) != item["sha256"]
                or sha(project / item["source_path"]) != item["source_sha256"]):
            raise SystemExit(f"LEAN_DEPENDENCY_CHANGED:{relative}")
    for row in rows:
        name = row["rocq_declaration"].split(".")[-1]
        audit = assumptions[name]
        if (row["acceptance"] != "ACCEPTED_V06_TRANSLATION"
                or audit["status"] != "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                or audit["semantic_premises"] or audit["unexpected"]
                or audit["statement_only_dependencies"]
                or audit["source_theorem_dependency"]
                or audit["target_theorem_dependency"]
                or lean_audit["declarations"][row["lean_declaration"]]["status"] != "PASS"
                or row["semantic_status"] != audit["status"]
                or row["fresh_olean_sha256"] !=
                   sha(work / "olean/Prosa/Util/Superadditivity.olean")
                or row["export_sha256"] != sha(work / "imported/Superadditivity.out")
                or row["imported_vo_sha256"] !=
                   sha(work / "imported/ImportedSuperadditivity.vo")):
            raise SystemExit(f"DECLARATION_AUDIT_FAILED:{name}")

    destination = validation / "imported/translation_order/superadditivity"
    destination.mkdir(parents=True, exist_ok=True)
    publish_files = [
        (work / "imported/Superadditivity.out", destination / "Superadditivity.out"),
        (work / "imported/ImportedSuperadditivity.v", destination / "ImportedSuperadditivity.v"),
        (work / "imported/ImportedSuperadditivity.vo", destination / "ImportedSuperadditivity.vo"),
        (work / "olean/Prosa/Util/Superadditivity.olean", destination / "Superadditivity.olean"),
        (work / "olean/Validation/fixtures/translation_order/SuperadditivityComputationInterface.olean",
         destination / "SuperadditivityComputationInterface.olean"),
        (work / "source/OfficialSuperadditivityAll_extraction.json",
         destination / "OfficialSuperadditivityAll_extraction.json"),
        (work / "prepare_manifest.json", destination / "prepare_manifest.json"),
        (work / "prepare_run_evidence.json", destination / "prepare_run_evidence.json"),
        (work / "superadditivity_assumption_summary.json", destination / "assumption_summary.json"),
        (work / "superadditivity_lean_axiom_summary.json", destination / "lean_axiom_summary.json"),
    ]
    for module in ["SuperadditivityBaseCorrespondence",
                   "SuperadditivityEquivalenceCertificate",
                   "SuperadditivityArithmeticCertificate",
                   "SuperadditivityMonotoneCertificate",
                   "SuperadditivityExtensionOperations",
                   "SuperadditivityHorizonCertificate",
                   "SuperadditivityEquivalenceTypeAudit",
                   "SuperadditivitySourceBindingAudit",
                   "SuperadditivityBaseAssumptionAudit"]:
        publish_files.append((work / "certificates" / f"{module}.vo",
                              destination / f"{module}.vo"))
    for source, target in publish_files:
        expected = sha(source)
        shutil.copy2(source, target)
        if sha(target) != expected:
            raise SystemExit(f"PUBLICATION_COPY_CORRUPT:{target}")
    published = {target.name: sha(target) for _, target in publish_files}
    manifest = {
        "slice": "TRANSLATION_ORDER_UTIL_SUPERADDITIVITY",
        "generated_at": datetime.now().astimezone().isoformat(),
        "source_file": "util/superadditivity.v",
        "source_commit": cluster["source_commit"],
        "source_file_sha256": cluster["source_sha256"],
        "production_file": "Prosa/Util/Superadditivity.lean",
        "production_source_sha256": cluster["lean_source_sha256"],
        "production_olean_sha256": cluster["fresh_olean_sha256"],
        "export_sha256": cluster["export_sha256"],
        "import_sha256": cluster["imported_vo_sha256"],
        "source_acquisition_metadata_sha256": cluster["source_acquisition_metadata_sha256"],
        "cluster_evidence_sha256": sha(cluster_path),
        "lean_source_build_manifest_sha256": sha(work / "lean_source_build_manifest.json"),
        "prepare_manifest_sha256": sha(work / "prepare_manifest.json"),
        "prepare_evidence_sha256": sha(work / "prepare_run_evidence.json"),
        "assumption_summary_sha256": sha(work / "superadditivity_assumption_summary.json"),
        "lean_axiom_summary_sha256": sha(work / "superadditivity_lean_axiom_summary.json"),
        "baseline_audit_sha256": sha(work / "superadditivity_baseline_audit.json"),
        "published_artifact_hashes": published,
        "snapshot_id": prepared["snapshot_id"],
        "fresh_build": True,
        "declarations": rows,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = pipeline / "util_superadditivity_module_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    coverage = dict(previous["coverage"])
    coverage["accepted_files"] += 1
    coverage["accepted_declarations"] += 12
    status = {
        "slice": "TRANSLATION_ORDER_UTIL_SUPERADDITIVITY",
        "snapshot_id": prepared["snapshot_id"],
        "per_file": {"util/superadditivity.v": {
            "public_declarations": 12, "translated": 12, "proof_clean": 12,
            "certified": 0, "certified_with_prop_sprop_foundation": 12,
            "accepted": 12, "status": "ACCEPTED_V06_FILE"}},
        "coverage": coverage,
        "previous_status_sha256": sha(previous_path),
        "manifest_sha256": sha(manifest_path),
        "status": "PASS",
    }
    status_path = pipeline / "util_superadditivity_module_status.json"
    status_path.write_text(json.dumps(status, indent=2) + "\n")
    print(f"SUPERADDITIVITY_ACCEPTED:12;PROJECT:{coverage['accepted_declarations']}/2439;")


if __name__ == "__main__":
    main()
