#!/usr/bin/env python3
"""Fail-closed publication of Rank 38 finish_time, five public declarations."""

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
WORK = PROJECT / "Validation/.work/experiments/analysis_finish_time"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE_FILE = "analysis/definitions/finish_time.v"
MODULE = "Prosa.Analysis.Definitions.FinishTime"
NAMES = ["finish_time", "finished_at_finish_time", "earliest_finish_time",
         "completes_at_finish_time", "response_time"]
CERTS = {
    "finish_time": "finish_time_correspondence",
    "finished_at_finish_time": "finished_at_finish_time_statement_correspondence",
    "earliest_finish_time": "earliest_finish_time_statement_correspondence",
    "completes_at_finish_time": "completes_at_finish_time_statement_correspondence",
    "response_time": "response_time_correspondence",
}


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise SystemExit(reason)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty artifact: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def data(path: Path) -> dict:
    sha(path)
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def without_proofs(source: str) -> str:
    return re.sub(r"Proof\.[\s\S]*?Qed\.", "Proof.<COMPATIBLE_PROOF>Qed.", source)


def main() -> None:
    selection = data(PIPELINE / "analysis_finish_time_selection.json")
    require(selection["rank"] == 38 and selection["file_dag_ready"]
            and selection["source_file"] == SOURCE_FILE
            and selection["targets_in_source_order"] == NAMES,
            "rank, DAG readiness, or target inventory mismatch")
    source = PROJECT / "Validation/.work/prosa-v06-414e667"
    require(command("git", "-C", str(source), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(source), "status", "--porcelain"),
            "official pinned source checkout is not clean")
    original = source / SOURCE_FILE
    source_sha = sha(original)
    require(source_sha == selection["source_sha256"], "official source changed")
    copy = WORK / "source/analysis/definitions/finish_time.v"
    require(without_proofs(original.read_text()) == without_proofs(copy.read_text()),
            "Rocq 9.3 compatibility copy changed a statement or computational body")
    patch = PROJECT / "Validation/patches/prosa-v06-rocq93-analysis-finish-time.patch"
    sha(patch)
    require("analysis/definitions/finish_time.v" in
            command("patch", "--dry-run", "--forward", "-p1", "-d", str(source),
                    "-i", str(patch)),
            "Rocq 9.3 compatibility patch cannot be applied to pinned source")

    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream) if row["source_file"] == SOURCE_FILE]
    require([row["declaration_name"] for row in rows] == NAMES,
            "official public declaration inventory changed")
    type_evidence = data(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
                f"elaborated source type evidence mismatch: {row['declaration_name']}")

    prior = data(PIPELINE / "analysis_completion_sequence_module_status.json")
    require(prior["status"] == "PASS" and prior["coverage"]["accepted_files"] == 36
            and prior["coverage"]["accepted_declarations"] == 317,
            "previous publication baseline invalid")
    service = data(PIPELINE / "behavior_service_module_manifest.json")
    require(service["acceptance"] == "ACCEPTED_V06_FILE"
            and sha(PROJECT / service["production_file"])
            == service["production_source_sha256"],
            "Service dependency is stale or not accepted")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version"),
            "Lean toolchain changed")
    require(command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474",
            "Mathlib revision changed")
    require("9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                              "rocq", "--version"), "Rocq version changed")
    tooling = data(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"], "exporter changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"], "importer changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "importer foundation changed")

    production = PROJECT / "Prosa/Analysis/Definitions/FinishTime.lean"
    olean = WORK / "olean/Prosa/Analysis/Definitions/FinishTime.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/FinishTimeExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/FinishTimeExportInterface.olean"
    for path in (production, olean, wrapper, wrapper_olean):
        sha(path)
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "stale compiled Lean artifact")
    lean_audit = (WORK / "lean_audit.log").read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit,
            "Lean proof-clean audit failed")
    for name in NAMES:
        match = re.search(r"'" + re.escape(MODULE + "." + name)
                          + r"' depends on axioms: \[([^\]]*)\]", lean_audit, re.S)
        require(match is not None and
                {x.strip() for x in match.group(1).split(",")}
                <= {"propext", "Classical.choice", "Quot.sound"},
                f"missing/unclean Lean #print axioms: {name}")

    export_config = PROJECT / "Validation/tooling/analysis_finish_time_export_config.json"
    config = data(export_config)
    metadata = data(WORK / "export_metadata.json")
    export = WORK / "FinishTime.out"
    require(metadata["config_sha256"] == sha(export_config)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 3
            and metadata["body_theorem_count"] == 4
            and len(metadata["normalization"]["body_projections"]) == 12
            and all(MODULE + "." + name in config["definition_targets"]
                    for name in ("finish_time", "response_time"))
            and all(MODULE + "." + name in config["statement_only"]
                    for name in NAMES[1:4]),
            "exact compiled Lean export/config invalid")
    imported = WORK / "ImportedFinishTime.v"
    imported_vo = WORK / "ImportedFinishTime.vo"
    require('Lean Import "Validation/.work/experiments/analysis_finish_time/FinishTime.out".'
            in imported.read_text(), "Rocq import points to another artifact")
    require(export.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "Rocq imported .vo predates export")

    cert = PROJECT / "Validation/certificates/analysis/FinishTimeCorrespondence.v"
    min_bridge = PROJECT / "Validation/certificates/analysis/FinishTimeMinBridge.v"
    guards = PROJECT / "Validation/certificates/analysis/FinishTimeExactTypeGuards.v"
    audit = PROJECT / "Validation/certificates/analysis/FinishTimeAssumptionAudit.v"
    audit_config = PROJECT / "Validation/certificates/analysis/finish_time_assumption_config.json"
    for path in (production, cert, min_bridge, guards, audit):
        text = path.read_text()
        require(not any(token in text for token in ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden placeholder/axiom: {path}")
    cert_text = cert.read_text()
    require("@prosa.analysis.definitions.finish_time.finish_time" in cert_text
            and "ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time"
            in cert_text and "minimum_value_correspondence" in cert_text
            and "completed_by_correspondence" in cert_text
            and "completes_at_correspondence" in cert_text,
            "semantic certificate is not compositionally bound to both actual artifacts")
    for name in NAMES[1:4]:
        require("@prosa.analysis.definitions.finish_time." + name not in cert_text
                and "ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_" + name
                not in cert_text, f"theorem self-dependency in correspondence: {name}")
    for path in (min_bridge, cert, guards, audit):
        require(path.stat().st_mtime_ns < path.with_suffix(".vo").stat().st_mtime_ns,
                f"stale certificate .vo: {path}")
    require(sha(WORK / "source/analysis/definitions/finish_time.vo")
            and sha(WORK / "FinishTimeSourceTypeAudit.vo")
            and sha(WORK / "FinishTimeImportedInspection.vo"),
            "source/target type inspection missing")
    summary = data(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "assumption audit not fail-closed")
    records = summary["certificates"]
    for name in ["minimum_value", *NAMES]:
        rec = records[name]
        require(rec["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and rec["prop_sprop_foundation"] ==
                ["PropSPropFoundation.interpret_strict"]
                and not rec["semantic_premises"]
                and not rec["statement_only_dependencies"]
                and not rec["source_theorem_dependency"]
                and not rec["target_theorem_dependency"]
                and not rec["unexpected"], f"unclean Rocq assumption audit: {name}")
    require(not command("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")

    artifacts = {
        "source_copy": copy, "source_vo": WORK / "source/analysis/definitions/finish_time.vo",
        "compatibility_patch": patch,
        "source_type_guard_vo": WORK / "FinishTimeSourceTypeAudit.vo",
        "target_type_inspection_vo": WORK / "FinishTimeImportedInspection.vo",
        "production_source": production, "production_olean": olean,
        "export_wrapper_source": wrapper, "export_wrapper_olean": wrapper_olean,
        "lean_audit_log": WORK / "lean_audit.log",
        "export_config": export_config, "export_metadata": WORK / "export_metadata.json",
        "export": export, "imported_source": imported, "imported_vo": imported_vo,
        "minimum_bridge_source": min_bridge, "minimum_bridge_vo": min_bridge.with_suffix(".vo"),
        "correspondence_source": cert, "correspondence_vo": cert.with_suffix(".vo"),
        "exact_type_guards_source": guards, "exact_type_guards_vo": guards.with_suffix(".vo"),
        "assumption_audit_source": audit, "assumption_audit_vo": audit.with_suffix(".vo"),
        "assumption_config": audit_config,
        "assumption_summary": WORK / "assumption_summary.json",
    }
    for filename in ("ServiceBaseAdapter", "ServiceNatBoolOperations",
                     "ServiceIntervalOperations", "ServiceScheduleOperations",
                     "ServiceJobOperations", "ServiceCorrespondence"):
        artifacts[f"replayed_{filename}_source"] = WORK / f"certificates/{filename}.v"
        artifacts[f"replayed_{filename}_vo"] = WORK / f"certificates/{filename}.vo"
    hashes = {name + "_sha256": sha(path) for name, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_FINISH_TIME", "source_commit": PIN,
        "source_file": SOURCE_FILE, "source_file_sha256": source_sha,
        "source_compatibility": "Rocq 9.3 proof-script-only patch; statements and computational bodies identical",
        "production_file": "Prosa/Analysis/Definitions/FinishTime.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": MODULE + "." + row["declaration_name"],
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": CERTS[row["declaration_name"]],
            "semantic_status": records[row["declaration_name"]]["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": records[row["declaration_name"]]["prop_sprop_foundation"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION"
        } for row in rows],
        "artifact_hashes": hashes,
        "tooling_manifest_sha256": sha(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE_FILE: {
            "public_declarations": 5, "translated": 5, "proof_clean": 5,
            "certified": 5, "certified_without_prop_sprop_foundation": 0,
            "certified_with_prop_sprop_foundation": 5,
            "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**prior["coverage"], "accepted_files": 37,
                     "accepted_declarations": 322,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPELINE / "analysis_finish_time_module_manifest.json"
    status_path = PIPELINE / "analysis_finish_time_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "declarations": len(manifest["declarations"]),
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
