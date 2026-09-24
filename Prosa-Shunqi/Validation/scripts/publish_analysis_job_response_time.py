#!/usr/bin/env python3
"""Fail-closed publication of the pinned Rank 45 Boolean definition."""

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
WORK = PROJECT / "Validation/.work/experiments/analysis_job_response_time"
PRODUCER = PROJECT / "Validation/.work/runs/behavior_all_finalize.djIKMA"
SOURCE = "analysis/definitions/job_response_time.v"
TARGET = "Prosa.Analysis.Definitions.JobResponseTime.job_response_time_exceeds"
IMPORTED = "Prosa_Analysis_Definitions_JobResponseTime_job_response_time_exceeds"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def digest(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def data(path: Path) -> dict:
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selected = data(PIPELINE / "analysis_job_response_time_selection.json")
    require(selected["rank"] == 45 and selected["source_file"] == SOURCE
            and selected["file_dag_ready"]
            and selected["targets_in_source_order"] == ["job_response_time_exceeds"],
            "selection/DAG mismatch")
    source_root = PROJECT / "Validation/.work/prosa-v06-414e667"
    official = source_root / SOURCE
    require(command("git", "-C", str(source_root), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(source_root), "status", "--porcelain")
            and digest(official) == selected["source_sha256"],
            "official source dirty, wrong commit, or changed")
    source_copy = WORK / "source" / SOURCE
    require(digest(source_copy) == digest(official),
            "source copy is not byte-identical official v0.6")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as f:
        rows = [r for r in csv.DictReader(f) if r["source_file"] == SOURCE]
    require(len(rows) == 1 and rows[0]["declaration_name"] == "job_response_time_exceeds"
            and rows[0]["kind"] == "Definition", "source inventory mismatch")
    type_evidence = data(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    row = rows[0]
    require(row["final_type_or_type_fingerprint"] ==
            "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
            "official elaborated type fingerprint mismatch")
    previous = data(PIPELINE / "analysis_schedule_prefix_module_status.json")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 43
            and previous["coverage"]["accepted_declarations"] == 339,
            "published baseline changed")
    accepted_all = data(PIPELINE / "behavior_all_module_manifest.json")
    require(accepted_all["acceptance"] == "ACCEPTED_V06_FILE"
            and accepted_all["source_commit"] == PIN
            and digest(PROJECT / accepted_all["production_file"]) ==
                accepted_all["production_source_sha256"]
            and digest(PRODUCER / "olean/Prosa/Behavior/All.olean") ==
                accepted_all["production_olean_sha256"],
            "Behavior.All producer is not hash-accepted")
    for path in (PRODUCER / "olean/Prosa").rglob("*.olean"):
        relative = path.relative_to(PRODUCER / "olean")
        require(digest(path) == digest(WORK / "olean" / relative),
                f"accepted dependency artifact changed: {relative}")
    for path in (PRODUCER / "olean/Validation").rglob("*.olean"):
        relative = path.relative_to(PRODUCER / "olean")
        require(digest(path) == digest(WORK / "olean" / relative),
                f"accepted interface artifact changed: {relative}")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version")
            and command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                        "rev-parse", "HEAD") ==
                "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                                 "rocq", "--version"), "toolchain mismatch")
    tooling = data(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(digest(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and digest(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and digest(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Analysis/Definitions/JobResponseTime.lean"
    olean = WORK / "olean/Prosa/Analysis/Definitions/JobResponseTime.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/JobResponseTimeExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/JobResponseTimeExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "Lean snapshot stale")
    lean_audit = WORK / "lean_audit.log"
    lean_text = lean_audit.read_text()
    require("error:" not in lean_text and "sorryAx" not in lean_text
            and TARGET in lean_text and "!Prosa.Behavior.Service.completed_by" in lean_text,
            "Lean computation/proof audit failed")
    axioms = re.search(r"'" + re.escape(TARGET) +
                       r"' depends on axioms: \[([^\]]*)\]", lean_text, re.S)
    require(axioms is not None and
            {a.strip() for a in axioms.group(1).split(",")}
            <= {"propext", "Classical.choice", "Quot.sound"},
            "Lean axiom allowlist failed")
    config_path = PROJECT / "Validation/tooling/analysis_job_response_time_export_config.json"
    config = data(config_path)
    export = WORK / "JobResponseTime.out"
    metadata = data(WORK / "export_metadata.json")
    require(config["module"] ==
            "Validation.fixtures.translation_order.JobResponseTimeExportInterface"
            and TARGET in config["definition_targets"]
            and metadata["config_sha256"] == digest(config_path)
            and metadata["output_sha256"] == digest(export)
            and metadata["statement_only_count"] == 0,
            "actual export/config mismatch")
    imported = WORK / "imported/ImportedJobResponseTime.v"
    imported_vo = WORK / "imported/ImportedJobResponseTime.vo"
    require('Lean Import "Validation/.work/experiments/analysis_job_response_time/JobResponseTime.out".'
            in imported.read_text()
            and export.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "imported artifact stale or wrong")
    cert_dir = PROJECT / "Validation/certificates/analysis"
    cert = cert_dir / "JobResponseTimeCorrespondence.v"
    guard = cert_dir / "JobResponseTimeExactTypeGuards.v"
    audit = cert_dir / "JobResponseTimeAssumptionAudit.v"
    audit_config = cert_dir / "job_response_time_assumption_config.json"
    for path in (production, cert, guard, audit):
        require(not any(t in path.read_text() for t in
                        ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden escape: {path}")
    require(IMPORTED in cert.read_text() and row["qualified_name"] in cert.read_text()
            and "completed_by_correspondence" not in cert.read_text()
            and "job_response_time_bound_correspondence" in cert.read_text(),
            "correspondence is not structural/reusing accepted bridge")
    for path in (cert, guard, audit):
        copy = WORK / "certificates" / path.name
        require(digest(path) == digest(copy)
                and copy.stat().st_mtime_ns < copy.with_suffix(".vo").stat().st_mtime_ns,
                f"certificate/guard/audit stale: {path}")
    guard_log = WORK / "JobResponseTimeExactTypeGuards.log"
    require("@job_response_time_exceeds" in guard_log.read_text()
            and IMPORTED in guard_log.read_text(), "exact type guard log missing")
    summary = data(WORK / "assumption_summary.json")
    expected = {
        "job_response_time_exceeds": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
        "completed_by_dependency": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
        "job_arrival_dependency": "CERTIFIED",
        "bool_not_dependency": "CERTIFIED",
    }
    require(summary["audit_policy"] == "fail_closed", "audit policy changed")
    for key, status in expected.items():
        rec = summary["certificates"][key]
        require(rec["status"] == status and not rec["semantic_premises"]
                and not rec["statement_only_dependencies"]
                and not rec["source_theorem_dependency"]
                and not rec["target_theorem_dependency"]
                and not rec["unexpected"], f"unclean assumption audit: {key}")
    require(not command("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")
    artifacts = {
        "official_source": official, "source_copy": source_copy,
        "source_vo": source_copy.with_suffix(".vo"),
        "production_source": production, "production_olean": olean,
        "export_wrapper": wrapper, "export_wrapper_olean": wrapper_olean,
        "lean_audit": lean_audit, "export_config": config_path,
        "export_metadata": WORK / "export_metadata.json", "export": export,
        "imported_source": imported, "imported_vo": imported_vo,
        "certificate": cert, "certificate_vo": WORK / "certificates/JobResponseTimeCorrespondence.vo",
        "exact_type_guard": guard,
        "exact_type_guard_vo": WORK / "certificates/JobResponseTimeExactTypeGuards.vo",
        "assumption_audit": audit,
        "assumption_audit_vo": WORK / "certificates/JobResponseTimeAssumptionAudit.vo",
        "assumption_config": audit_config,
        "assumption_summary": WORK / "assumption_summary.json",
        "behavior_all_manifest": PIPELINE / "behavior_all_module_manifest.json",
    }
    hashes = {key + "_sha256": digest(path) for key, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_JOB_RESPONSE_TIME", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": digest(official),
        "source_compatibility": "byte-identical official source; no patch",
        "production_file": "Prosa/Analysis/Definitions/JobResponseTime.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"], "lean_declaration": TARGET,
            "kind": "Definition", "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": "job_response_time_exceeds_correspondence",
            "semantic_status": expected["job_response_time_exceeds"],
            "input_relations": ["SvcProcessorStateRel", "SvcScheduleRel",
                                "SvcJobCostRel", "SvcJobArrivalRel", "SubNatRel"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION",
        }],
        "artifact_hashes": hashes,
        "tooling_manifest_sha256": digest(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 1, "translated": 1, "proof_clean": 1,
            "certified": 1, "certified_with_prop_sprop_foundation": 1,
            "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**previous["coverage"], "accepted_files": 44,
                     "accepted_declarations": 340,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPELINE / "analysis_job_response_time_module_manifest.json"
    status_path = PIPELINE / "analysis_job_response_time_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = digest(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
