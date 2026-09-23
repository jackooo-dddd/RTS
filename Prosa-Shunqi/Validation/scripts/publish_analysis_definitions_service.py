#!/usr/bin/env python3
"""Fail-closed publication of pinned analysis/definitions/service.v."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import subprocess
from datetime import datetime, timedelta, timezone
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
WORK = PROJECT / "Validation/.work/experiments/analysis_definitions_service"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE_FILE = "analysis/definitions/service.v"
MODULE = "Prosa.Analysis.Definitions.Service"
NAMES = ["served_jobs_at", "served_job_at"]
REPLAY = ["ServiceBaseAdapter", "ServiceNatBoolOperations",
          "ServiceIntervalOperations", "ServiceScheduleOperations",
          "ServiceJobOperations", "ServiceCorrespondence",
          "ArrivalSequenceBaseAdapter", "ArrivalSequenceOperations",
          "ArrivalSequenceCorrespondence"]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    sha(path)
    return json.loads(path.read_text())


def cmd(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read(PIPELINE / "analysis_service_selection.json")
    require(selection["rank"] == 42 and selection["file_dag_ready"]
            and selection["source_file"] == SOURCE_FILE
            and selection["targets_in_source_order"] == NAMES,
            "selection/file-DAG mismatch")
    source_root = PROJECT / "Validation/.work/prosa-v06-414e667"
    require(cmd("git", "-C", str(source_root), "rev-parse", "HEAD") == PIN
            and not cmd("git", "-C", str(source_root), "status", "--porcelain"),
            "pinned source checkout changed")
    official = source_root / SOURCE_FILE
    source_copy = WORK / "source" / SOURCE_FILE
    require(sha(official) == selection["source_sha256"]
            and sha(source_copy) == sha(official),
            "Rocq source is not byte-identical to pinned official declaration file")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE_FILE]
    require([r["declaration_name"] for r in rows] == NAMES
            and all(r["kind"] == "Definition" for r in rows),
            "source public-declaration inventory changed")
    type_evidence = read(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
                f"source elaborated type changed: {row['declaration_name']}")
    previous = read(PIPELINE / "analysis_sbf_pred_module_status.json")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 40
            and previous["coverage"]["accepted_declarations"] == 331,
            "prior publication baseline invalid")
    for name, module in (("behavior_service", "Service"),
                         ("behavior_arrival_sequence", "Arrival_sequence")):
        manifest = read(PIPELINE / f"{name}_module_manifest.json")
        require(manifest["acceptance"] == "ACCEPTED_V06_FILE"
                and sha(PROJECT / manifest["production_file"])
                == manifest["production_source_sha256"]
                and sha(WORK / f"olean/Prosa/Behavior/{module}.olean")
                == manifest["production_olean_sha256"],
                f"reused accepted {name} artifact/source changed")
    require("Lean (version 4.33.1" in cmd("lake", "env", "lean", "--version")
            and cmd("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in cmd("opam", "exec", "--switch=rocq93rc1", "--",
                             "rocq", "--version"),
            "toolchain version changed")
    tooling = read(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "import/export tool identity changed")

    production = PROJECT / "Prosa/Analysis/Definitions/Service.lean"
    olean = WORK / "olean/Prosa/Analysis/Definitions/Service.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/AnalysisServiceExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/AnalysisServiceExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "stale Lean compiled artifact")
    lean_log = WORK / "lean_audit.log"
    lean_text = lean_log.read_text()
    require("error:" not in lean_text and "sorryAx" not in lean_text,
            "Lean proof-clean audit failed")
    for name in NAMES:
        match = re.search(r"'" + re.escape(MODULE + "." + name)
                          + r"' depends on axioms: \[([^\]]*)\]", lean_text, re.S)
        require(match is not None and {
                    re.sub(r"\.\{[^}]*\}$", "", s.strip())
                    for s in match.group(1).split(",")}
                <= {"propext", "Classical.choice", "Quot.sound"},
                f"unexpected Lean axiom or missing audit: {name}")
    config_path = PROJECT / "Validation/tooling/analysis_definitions_service_export_config.json"
    config = read(config_path)
    metadata = read(WORK / "export_metadata.json")
    export = WORK / "AnalysisService.out"
    require(config["module"] == "Validation.fixtures.translation_order.AnalysisServiceExportInterface"
            and all(MODULE + "." + n in config["definition_targets"] for n in NAMES)
            and not config["statement_only"]
            and metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 0
            and len(metadata["normalization"]["body_projections"]) == 12,
            "actual definition-body export/config invalid")
    imported_source = WORK / "ImportedAnalysisService.v"
    imported_vo = WORK / "ImportedAnalysisService.vo"
    require('Lean Import "Validation/.work/experiments/analysis_definitions_service/AnalysisService.out".'
            in imported_source.read_text()
            and export.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "imported module is stale or points to wrong export")
    cert = PROJECT / "Validation/certificates/analysis/AnalysisServiceCorrespondence.v"
    audit = PROJECT / "Validation/certificates/analysis/AnalysisServiceAssumptionAudit.v"
    audit_config = PROJECT / "Validation/certificates/analysis/analysis_service_assumption_config.json"
    for path in (production, cert, audit):
        require(not any(token in path.read_text() for token in
                        ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden proof escape: {path}")
    proof = cert.read_text()
    require(all("prosa.analysis.definitions.service." + n in proof
                and "ImportedAnalysisService.Prosa_Analysis_Definitions_Service_" + n in proof
                for n in NAMES)
            and "arrivals_up_to_correspondence_certificate" in proof
            and "receives_service_at_correspondence" in proof
            and "ar_filter_related" in proof
            and "as_ohead_correspondence" in proof,
            "certificate does not compose direct actual-artifact relations")
    work_cert = WORK / "certificates/AnalysisServiceCorrespondence.v"
    work_audit = WORK / "certificates/AnalysisServiceAssumptionAudit.v"
    require(sha(cert) == sha(work_cert) and sha(audit) == sha(work_audit)
            and work_cert.stat().st_mtime_ns < work_cert.with_suffix(".vo").stat().st_mtime_ns
            and work_audit.stat().st_mtime_ns < work_audit.with_suffix(".vo").stat().st_mtime_ns,
            "Rocq certificate/audit copy or compiled .vo stale")
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "assumption policy changed")
    require(summary["certificates"]["as_ohead"]["status"] == "CERTIFIED",
            "head operation bridge did not close")
    for name in NAMES:
        record = summary["certificates"][name]
        require(record["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and record["prop_sprop_foundation"] ==
                ["PropSPropFoundation.interpret_strict"]
                and not record["semantic_premises"]
                and not record["statement_only_dependencies"]
                and not record["source_theorem_dependency"]
                and not record["target_theorem_dependency"]
                and not record["unexpected"],
                f"unclean assumption closure: {name}")
    require(not cmd("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")
    artifacts = {
        "source_copy": source_copy, "source_vo": source_copy.with_suffix(".vo"),
        "source_inspection_vo": WORK / "AnalysisServiceSourceInspection.vo",
        "target_inspection_vo": WORK / "AnalysisServiceImportedInspection.vo",
        "production_source": production, "production_olean": olean,
        "wrapper_source": wrapper, "wrapper_olean": wrapper_olean,
        "lean_audit_log": lean_log, "export_config": config_path,
        "export_metadata": WORK / "export_metadata.json", "export": export,
        "imported_source": imported_source, "imported_vo": imported_vo,
        "certificate_source": cert, "certificate_vo": work_cert.with_suffix(".vo"),
        "assumption_audit_source": audit, "assumption_audit_vo": work_audit.with_suffix(".vo"),
        "assumption_config": audit_config,
        "assumption_summary": WORK / "assumption_summary.json",
    }
    for name in REPLAY:
        replay = WORK / "certificates" / f"{name}.v"
        producer = (PROJECT / "Validation/certificates" /
                    ("behavior_service" if name.startswith("Service")
                     else "behavior_arrival_sequence") / f"{name}.v")
        require(sha(producer) in replay.read_text()
                and "ImportedAnalysisService" in replay.read_text()
                and replay.stat().st_mtime_ns < replay.with_suffix(".vo").stat().st_mtime_ns,
                f"accepted bridge replay invalid: {name}")
        artifacts[f"replayed_{name}_source"] = replay
        artifacts[f"replayed_{name}_vo"] = replay.with_suffix(".vo")
    hashes = {key + "_sha256": sha(path) for key, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_DEFINITIONS_SERVICE",
        "source_commit": PIN, "source_file": SOURCE_FILE,
        "source_file_sha256": sha(official),
        "source_compatibility": "byte-identical official source; directly compiled in Rocq 9.3",
        "production_file": "Prosa/Analysis/Definitions/Service.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": MODULE + "." + name,
            "kind": "Definition",
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": name + "_correspondence",
            "semantic_status": summary["certificates"][name]["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION",
        } for name, row in zip(NAMES, rows)],
        "artifact_hashes": hashes,
        "tooling_manifest_sha256": sha(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE_FILE: {
            "public_declarations": 2, "translated": 2, "proof_clean": 2,
            "certified": 2, "certified_without_prop_sprop_foundation": 0,
            "certified_with_prop_sprop_foundation": 2,
            "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**previous["coverage"], "accepted_files": 41,
                     "accepted_declarations": 333,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPELINE / "analysis_service_module_manifest.json"
    status_path = PIPELINE / "analysis_service_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "declarations": 2, "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
