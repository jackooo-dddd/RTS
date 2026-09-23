#!/usr/bin/env python3
"""Fail-closed Rank 41 publication: four definitions and one theorem type."""

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
WORK = PROJECT / "Validation/.work/experiments/analysis_sbf_pred"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
FILE = "analysis/definitions/sbf/pred.v"
MODULE = "Prosa.Analysis.Definitions.Sbf.Pred"
NAMES = ["pred_sbf_respected", "valid_pred_sbf", "sbf_is_monotone",
         "unit_supply_bound_function", "sbf_bounded_by_duration"]
CERTS = ["pred_sbf_respected_correspondence",
         "pred_valid_pred_sbf_correspondence",
         "pred_sbf_is_monotone_correspondence",
         "pred_unit_supply_bound_function_correspondence",
         "pred_sbf_bounded_by_duration_statement_correspondence"]
PRODUCER = PROJECT / "Validation/.work/incremental/model_processor_supply/592b3619f31955d0c4b7b87798f4e43c45e879af7946b4a6e386c9d0c88bbb09"
ARRIVAL_PRODUCER = PROJECT / "Validation/.work/incremental/behavior_arrival_sequence/c1d257c3b0ec6199ee42ca57b25a48c34cfea4514dfdd98249295bc68b32b78e"
REPLAY = ["SupplyBaseAdapter", "SupplyScheduleBaseAdapter",
          "SupplyScheduleFiniteOperations", "SupplyScheduleOperations",
          "SupplyNatBoolOperations", "SupplyIntervalOperations",
          "SupplyCorrespondence", "ArrivalSequenceBaseAdapter",
          "ArrivalSequenceOperations", "ArrivalSequenceCorrespondence"]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    sha(path)
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read(PIPELINE / "analysis_sbf_pred_selection.json")
    require(selection["rank"] == 41 and selection["file_dag_ready"]
            and selection["source_file"] == FILE
            and selection["targets_in_source_order"] == NAMES,
            "selection/order/inventory mismatch")
    source = PROJECT / "Validation/.work/prosa-v06-414e667"
    require(command("git", "-C", str(source), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(source), "status", "--porcelain"),
            "authoritative source checkout not pinned/clean")
    official = source / FILE
    require(sha(official) == selection["source_sha256"], "authoritative source changed")
    source_copy = WORK / "source/analysis/definitions/sbf/pred.v"
    expected = official.read_text().replace(
        "Require Export prosa.analysis.definitions.sbf.sbf.\n",
        "Require Export prosa.analysis.definitions.sbf.sbf.\n"
        "Require Import prosa.util.rel.\nRequire Import prosa.util.setoid.\n", 1)
    require(source_copy.read_text() == expected,
            "validation source patch changed a declaration/proof")
    for file in ("util/rel.v", "util/setoid.v",
                 "analysis/definitions/sbf/sbf.v"):
        require((WORK / "source" / file).read_text() == (source / file).read_text(),
                f"official supporting source changed: {file}")
    patch = PROJECT / "Validation/patches/prosa-v06-rocq93-analysis-sbf-pred.patch"
    require(FILE in command("patch", "--dry-run", "--forward", "-p1", "-d",
                            str(source), "-i", str(patch)),
            "compatibility patch does not apply to pinned source")
    require(sha(WORK / "source/util/all.vo") == sha(PRODUCER / "source/util/all.vo")
            and sha(WORK / "source/behavior/job.vo") == sha(PRODUCER / "source/behavior/job.vo"),
            "source dependency closure inconsistent")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == FILE]
    require([r["declaration_name"] for r in rows] == NAMES,
            "five-declaration public inventory mismatch")
    type_evidence = read(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
                f"official elaborated type fingerprint changed: {row['declaration_name']}")
    prior = read(PIPELINE / "analysis_sbf_periodic_module_status.json")
    require(prior["status"] == "PASS"
            and prior["coverage"]["accepted_files"] == 39
            and prior["coverage"]["accepted_declarations"] == 326,
            "previous publication baseline invalid")
    supply = read(PIPELINE / "model_processor_supply_module_manifest.json")
    sbf = read(PIPELINE / "analysis_sbf_sbf_module_manifest.json")
    arrival = read(PIPELINE / "behavior_arrival_sequence_module_manifest.json")
    for label, manifest in (("Supply", supply), ("SBF", sbf), ("Arrival", arrival)):
        require(manifest["acceptance"] == "ACCEPTED_V06_FILE"
                and sha(PROJECT / manifest["production_file"])
                == manifest.get("production_source_sha256",
                                manifest.get("artifact_hashes", {}).get("production_source_sha256")),
                f"accepted {label} dependency stale")
    require(sha(WORK / "olean/Prosa/Model/Processor/Supply.olean")
            == supply["production_olean_sha256"], "Supply .olean changed")
    require(sha(WORK / "olean/Prosa/Analysis/Definitions/Sbf/Sbf.olean")
            == sbf["artifact_hashes"]["production_olean_sha256"],
            "SBF class .olean changed")
    require(sha(WORK / "olean/Prosa/Behavior/Arrival_sequence.olean")
            == sha(ARRIVAL_PRODUCER / "olean/Prosa/Behavior/Arrival_sequence.olean"),
            "arrival .olean changed")
    for name in ("ArrivalSequenceComputationInterface", "BigcatComputationInterface"):
        require(sha(WORK / f"olean/Validation/fixtures/translation_order/{name}.olean")
                == sha(ARRIVAL_PRODUCER / f"olean/Validation/fixtures/translation_order/{name}.olean"),
                f"accepted arrival interface changed: {name}")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version"),
            "Lean changed")
    require(command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474", "Mathlib changed")
    require("9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                              "rocq", "--version"), "Rocq changed")
    tooling = read(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"], "exporter changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"], "importer changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "importer foundation changed")
    production = PROJECT / "Prosa/Analysis/Definitions/Sbf/Pred.lean"
    olean = WORK / "olean/Prosa/Analysis/Definitions/Sbf/Pred.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/PredExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/PredExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "stale target/interface Lean build")
    lean_audit = (WORK / "lean_audit.log").read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit,
            "Lean proof-clean audit failed")
    for name in NAMES:
        full = MODULE + "." + name
        require(full in lean_audit, f"missing Lean type/axiom audit: {full}")
        axiom_match = re.search(r"'" + re.escape(full)
                                + r"' depends on axioms: \[([^\]]*)\]", lean_audit, re.S)
        if axiom_match:
            require({x.strip() for x in axiom_match.group(1).split(",")}
                    <= {"propext", "Classical.choice", "Quot.sound"},
                    f"unexpected Lean axiom: {full}")
        else:
            require(f"'{full}' does not depend on any axioms" in lean_audit,
                    f"missing Lean axiom report: {full}")
    config_path = PROJECT / "Validation/tooling/analysis_sbf_pred_export_config.json"
    config = read(config_path)
    metadata = read(WORK / "export_metadata.json")
    export = WORK / "Pred.out"
    require(metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 1
            and config["statement_only"] == [MODULE + ".sbf_bounded_by_duration"]
            and all(MODULE + "." + n in config["definition_targets"] for n in NAMES[:4])
            and len(metadata["normalization"]["body_projections"]) == 5,
            "compiled export/config invalid")
    imported = WORK / "ImportedPred.v"
    imported_vo = WORK / "ImportedPred.vo"
    require('Lean Import "Validation/.work/experiments/analysis_sbf_pred/Pred.out".'
            in imported.read_text() and export.stat().st_mtime_ns
            < imported_vo.stat().st_mtime_ns, "imported artifact stale")
    cert = PROJECT / "Validation/certificates/analysis/PredCorrespondence.v"
    guard = PROJECT / "Validation/certificates/analysis/PredExactTypeGuards.v"
    audit = PROJECT / "Validation/certificates/analysis/PredAssumptionAudit.v"
    audit_config = PROJECT / "Validation/certificates/analysis/pred_assumption_config.json"
    for path in (production, cert, guard, audit):
        require(not any(x in path.read_text() for x in
                        ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden placeholder/axiom: {path}")
    proof = cert.read_text()
    require(all("prosa.analysis.definitions.sbf.pred." + n in proof
                and "ImportedPred.Prosa_Analysis_Definitions_Sbf_Pred_" + n in proof
                for n in NAMES[:4])
            and "supply_during_correspondence" in proof
            and "arrives_in_correspondence_certificate" in proof
            and "pred_bounded_statement_for_functions" in proof,
            "source/target structural proof composition missing")
    require("sbf_bounded_by_duration" not in proof.split("Proof.")[0]
            or "statement_correspondence" in proof,
            "theorem statement correspondence missing")
    require("From FoundationCertificates Require Import PredExactTypeGuards" not in proof,
            "semantic certificate imports self-dependent guard")
    require("prosa.analysis.definitions.sbf.pred.sbf_bounded_by_duration\n" not in proof
            and "ImportedPred.Prosa_Analysis_Definitions_Sbf_Pred_sbf_bounded_by_duration\n" not in proof,
            "semantic certificate directly names theorem proof constant")
    require("sbf_bounded_by_duration" in guard.read_text(),
            "separate exact-type guard missing")
    for path in (cert, guard, audit):
        require(path.stat().st_mtime_ns < path.with_suffix(".vo").stat().st_mtime_ns,
                f"stale Rocq certificate/guard/audit: {path}")
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "audit policy changed")
    for name in ["pred_interval", *NAMES]:
        record = summary["certificates"][name]
        require(record["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and record["prop_sprop_foundation"] ==
                ["PropSPropFoundation.interpret_strict"]
                and not record["semantic_premises"]
                and not record["statement_only_dependencies"]
                and not record["source_theorem_dependency"]
                and not record["target_theorem_dependency"]
                and not record["unexpected"],
                f"unclean semantic assumption audit: {name}")
    require(not command("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")
    artifacts = {
        "source_copy": source_copy, "source_vo": source_copy.with_suffix(".vo"),
        "source_inspection_vo": WORK / "PredSourceInspection.vo",
        "target_inspection_vo": WORK / "PredImportedInspection.vo",
        "compatibility_patch": patch,
        "production_source": production, "production_olean": olean,
        "wrapper_source": wrapper, "wrapper_olean": wrapper_olean,
        "lean_audit_log": WORK / "lean_audit.log",
        "export_config": config_path, "export_metadata": WORK / "export_metadata.json",
        "export": export, "imported_source": imported, "imported_vo": imported_vo,
        "certificate_source": cert, "certificate_vo": cert.with_suffix(".vo"),
        "guard_source": guard, "guard_vo": guard.with_suffix(".vo"),
        "audit_source": audit, "audit_vo": audit.with_suffix(".vo"),
        "audit_config": audit_config,
        "assumption_summary": WORK / "assumption_summary.json",
        "supply_reuse_evidence": WORK / "dependency_reuse_evidence.json",
        "supply_replay_evidence": WORK / "supply_replay.json",
        "arrival_replay_evidence": WORK / "arrival_replay.json",
    }
    for filename in REPLAY:
        artifacts[f"replayed_{filename}_source"] = WORK / f"certificates/{filename}.v"
        artifacts[f"replayed_{filename}_vo"] = WORK / f"certificates/{filename}.vo"
    hashes = {key + "_sha256": sha(path) for key, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_SBF_PRED", "source_commit": PIN,
        "source_file": FILE, "source_file_sha256": sha(official),
        "source_compatibility": "Rocq 9.3 direct imports of byte-identical official util/rel and util/setoid; public declarations unchanged",
        "production_file": "Prosa/Analysis/Definitions/Sbf/Pred.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": MODULE + "." + row["declaration_name"],
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": CERTS[i],
            "semantic_status": summary["certificates"][row["declaration_name"]]["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION"
        } for i, row in enumerate(rows)],
        "artifact_hashes": hashes,
        "tooling_manifest_sha256": sha(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {FILE: {
            "public_declarations": 5, "translated": 5, "proof_clean": 5,
            "certified": 5, "certified_without_prop_sprop_foundation": 0,
            "certified_with_prop_sprop_foundation": 5,
            "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**prior["coverage"], "accepted_files": 40,
                     "accepted_declarations": 331,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPELINE / "analysis_sbf_pred_module_manifest.json"
    status_path = PIPELINE / "analysis_sbf_pred_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "declarations": len(manifest["declarations"]),
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
