#!/usr/bin/env python3
"""Fail-closed publication of the pinned Rank 37 completion_sequence slice."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone, timedelta
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
WORK = PROJECT / "Validation/.work/experiments/analysis_completion_sequence"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE_FILE = "analysis/definitions/completion_sequence.v"
MODULE = "Prosa.Analysis.Definitions.CompletionSequence"
IMPORTED = "ImportedCompletionSequenceCombined"


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty artifact: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    sha(path)
    return json.loads(path.read_text())


def cmd(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read_json(PIPELINE / "analysis_completion_sequence_selection.json")
    require(selection["rank"] == 37 and selection["file_dag_ready"]
            and selection["source_file"] == SOURCE_FILE
            and selection["targets_in_source_order"] == ["completion_sequence"],
            "rank, file-DAG, or target inventory mismatch")
    source = PROJECT / "Validation/.work/prosa-v06-414e667"
    require(cmd("git", "-C", str(source), "rev-parse", "HEAD") == PIN
            and not cmd("git", "-C", str(source), "status", "--porcelain"),
            "official v0.6 source is not the clean pinned checkout")
    source_sha = sha(source / SOURCE_FILE)
    require(source_sha == selection["source_sha256"], "official source changed")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE_FILE]
    require(len(rows) == 1 and rows[0]["declaration_name"] == "completion_sequence"
            and rows[0]["kind"] == "Definition", "public inventory mismatch")
    row = rows[0]
    type_evidence = read_json(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    official_type = type_evidence[row["qualified_name"]]
    require(row["final_type_or_type_fingerprint"] == "rocq-check-sha256:" + official_type["sha256"],
            "official elaborated type fingerprint mismatch")

    previous = read_json(PIPELINE / "implementation_facts_extrapolated_arrival_curve_module_status.json")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 35
            and previous["coverage"]["accepted_declarations"] == 316,
            "previous publication baseline invalid")
    for name in ("behavior_service", "behavior_arrival_sequence"):
        manifest = read_json(PIPELINE / f"{name}_module_manifest.json")
        require(manifest["acceptance"] == "ACCEPTED_V06_FILE", f"unaccepted dependency: {name}")
        require(sha(PROJECT / manifest["production_file"])
                == manifest["production_source_sha256"], f"changed production dependency: {name}")

    require("Lean (version 4.33.1" in cmd("lake", "env", "lean", "--version"),
            "Lean toolchain changed")
    require(cmd("git", "-C", str(PROJECT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474",
            "Mathlib revision changed")
    require("9.3" in cmd("opam", "exec", "--switch=rocq93rc1", "--", "rocq", "--version"),
            "Rocq version changed")
    tooling = read_json(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"], "exporter changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"], "importer changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "importer foundation changed")

    source_meta = read_json(WORK / "source_metadata.json")
    source_record = source_meta["declarations"]["completion_sequence"]
    require(source_meta["source_commit"] == PIN
            and source_meta["source_file_sha256"] == source_sha
            and source_record["acquisition_mode"] == "BODY_EXACT"
            and source_record["source_block_sha256"] == row["source_command_sha256"]
            and source_record["generated_text_sha256"] == row["source_command_sha256"],
            "official computational body extraction mismatch")
    official_slice = WORK / "source/OfficialCompletionSequence.v"
    official_vo = official_slice.with_suffix(".vo")
    source_inspection = WORK / "CompletionSequenceSourceInspection.vo"
    target_inspection = WORK / "CompletionSequenceTypeInspection.vo"
    for path in (official_slice, official_vo, source_inspection, target_inspection):
        sha(path)

    production = PROJECT / "Prosa/Analysis/Definitions/CompletionSequence.lean"
    olean = WORK / "olean/Prosa/Analysis/Definitions/CompletionSequence.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/CompletionSequenceExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/CompletionSequenceExportInterface.olean"
    for path in (production, olean, wrapper, wrapper_olean):
        sha(path)
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "compiled artifact is stale")
    lean_audit = (WORK / "lean_audit.log").read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit,
            "Lean declaration audit failed")
    require(f"'{MODULE}.completion_sequence' depends on axioms: " in lean_audit,
            "missing Lean #print axioms")
    match = re.search(r"'" + re.escape(MODULE) + r"\.completion_sequence' depends on axioms: \[([^\]]*)\]",
                      lean_audit, re.S)
    require(match is not None and {s.strip() for s in match.group(1).split(",")}
            <= {"propext", "Classical.choice", "Quot.sound"},
            "unexpected Lean declaration axiom")

    config_path = PROJECT / "Validation/tooling/analysis_completion_sequence_combined_export_config.json"
    config = read_json(config_path)
    metadata = read_json(WORK / "combined_export_metadata.json")
    export = WORK / "CompletionSequenceCombined.out"
    require(config["module"] == "Validation.fixtures.translation_order.CompletionSequenceExportInterface"
            and MODULE + ".completion_sequence" in config["definition_targets"]
            and not config["statement_only"]
            and metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 0
            and len(metadata["normalization"]["body_projections"]) == 12,
            "actual compiled Lean export/config invalid")
    imported_source = WORK / f"{IMPORTED}.v"
    imported_vo = WORK / f"{IMPORTED}.vo"
    require(f'Lean Import "Validation/.work/experiments/analysis_completion_sequence/CompletionSequenceCombined.out".'
            in imported_source.read_text(), "imported module points to wrong export")
    require(export.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "imported .vo predates current export")

    cert = PROJECT / "Validation/certificates/analysis/CompletionSequenceCorrespondence.v"
    audit_source = PROJECT / "Validation/certificates/analysis/CompletionSequenceAssumptionAudit.v"
    audit_config = PROJECT / "Validation/certificates/analysis/completion_sequence_assumption_config.json"
    for path in (production, cert, audit_source):
        body = path.read_text()
        require(not any(token in body for token in ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden placeholder/axiom: {path}")
    cert_text = cert.read_text()
    require("@OfficialCompletionSequence.completion_sequence" in cert_text
            and f"{IMPORTED}.Prosa_Analysis_Definitions_CompletionSequence_completion_sequence"
            in cert_text and "arrivals_up_to_correspondence_certificate" in cert_text
            and "completes_at_correspondence" in cert_text
            and "ar_filter_related" in cert_text,
            "certificate lacks direct source/target or operation binding")
    summary = read_json(WORK / "assumption_summary.json")
    record = summary["certificates"]["completion_sequence"]
    require(summary["audit_policy"] == "fail_closed"
            and record["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
            and not record["semantic_premises"] and not record["statement_only_dependencies"]
            and not record["source_theorem_dependency"]
            and not record["target_theorem_dependency"]
            and not record["unexpected"]
            and record["prop_sprop_foundation"] == ["PropSPropFoundation.interpret_strict"],
            "semantic correspondence assumption audit failed")
    require(not cmd("git", "-C", str(ROOT), "diff", "--check"), "git diff --check failed")

    artifacts = {
        "source_slice": official_slice,
        "source_slice_vo": official_vo,
        "source_metadata": WORK / "source_metadata.json",
        "source_type_inspection_vo": source_inspection,
        "target_type_inspection_vo": target_inspection,
        "production_source": production,
        "production_olean": olean,
        "export_wrapper_source": wrapper,
        "export_wrapper_olean": wrapper_olean,
        "lean_audit_log": WORK / "lean_audit.log",
        "export_config": config_path,
        "export_metadata": WORK / "combined_export_metadata.json",
        "export": export,
        "imported_source": imported_source,
        "imported_vo": imported_vo,
        "certificate_source": cert,
        "certificate_vo": cert.with_suffix(".vo"),
        "assumption_audit_source": audit_source,
        "assumption_audit_vo": audit_source.with_suffix(".vo"),
        "assumption_config": audit_config,
        "assumption_summary": WORK / "assumption_summary.json",
    }
    for filename in ("ArrivalSequenceBaseAdapter", "ArrivalSequenceOperations",
                     "ArrivalSequenceCorrespondence", "ServiceBaseAdapter",
                     "ServiceNatBoolOperations", "ServiceIntervalOperations",
                     "ServiceScheduleOperations", "ServiceJobOperations",
                     "ServiceCorrespondence"):
        artifacts[f"replayed_{filename}_source"] = WORK / f"certificates/{filename}.v"
        artifacts[f"replayed_{filename}_vo"] = WORK / f"certificates/{filename}.vo"
    artifact_hashes = {name + "_sha256": sha(path) for name, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_COMPLETION_SEQUENCE",
        "source_commit": PIN,
        "source_file": SOURCE_FILE,
        "source_file_sha256": source_sha,
        "production_file": "Prosa/Analysis/Definitions/CompletionSequence.lean",
        "production_source_sha256": artifact_hashes["production_source_sha256"],
        "production_olean_sha256": artifact_hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": MODULE + ".completion_sequence",
            "kind": "Definition",
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": official_type["sha256"],
            "semantic_certificate": "completion_sequence_correspondence",
            "semantic_status": record["status"],
            "semantic_premises": [],
            "statement_only_dependencies": [],
            "prop_sprop_foundation": record["prop_sprop_foundation"],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "acceptance": "ACCEPTED_V06_TRANSLATION"
        }],
        "artifact_hashes": artifact_hashes,
        "tooling_manifest_sha256": sha(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE_FILE: {
            "public_declarations": 1, "translated": 1, "proof_clean": 1,
            "certified": 1, "certified_without_prop_sprop_foundation": 0,
            "certified_with_prop_sprop_foundation": 1,
            "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**previous["coverage"], "accepted_files": 36,
                     "accepted_declarations": 317,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPELINE / "analysis_completion_sequence_module_manifest.json"
    status_path = PIPELINE / "analysis_completion_sequence_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "semantic_status": record["status"],
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
