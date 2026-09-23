#!/usr/bin/env python3
"""Fail-closed Rank 39 whole-file publication for average-resource definitions."""

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
WORK = PROJECT / "Validation/.work/experiments/analysis_sbf_average"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
FILE = "analysis/definitions/sbf/average.v"
MODULE = "Prosa.Analysis.Definitions.Sbf.Average"
NAMES = ["average_resource_model", "arm_sbf"]
PRODUCER = PROJECT / "Validation/.work/incremental/model_processor_supply/592b3619f31955d0c4b7b87798f4e43c45e879af7946b4a6e386c9d0c88bbb09"


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
    selection = read(PIPELINE / "analysis_sbf_average_selection.json")
    require(selection["rank"] == 39 and selection["file_dag_ready"]
            and selection["source_file"] == FILE
            and selection["targets_in_source_order"] == NAMES,
            "selection/order/inventory mismatch")
    source = PROJECT / "Validation/.work/prosa-v06-414e667"
    require(command("git", "-C", str(source), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(source), "status", "--porcelain"),
            "authoritative source checkout not clean/pinned")
    official = source / FILE
    official_sha = sha(official)
    require(official_sha == selection["source_sha256"], "authoritative source changed")
    copy = WORK / "source/analysis/definitions/sbf/average.v"
    require(copy.read_text() == official.read_text().replace(
        "Require Export prosa.model.processor.supply.\n",
        "Require Export prosa.model.processor.supply.\nFrom mathcomp Require Import div.\n",
        1), "compatibility copy changed a declaration")
    patch = PROJECT / "Validation/patches/prosa-v06-rocq93-analysis-sbf-average.patch"
    require(FILE in command("patch", "--dry-run", "--forward", "-p1", "-d",
                            str(source), "-i", str(patch)),
            "compatibility patch does not apply to pinned source")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream) if row["source_file"] == FILE]
    require([row["declaration_name"] for row in rows] == NAMES,
            "public declaration inventory mismatch")
    type_evidence = read(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
                f"source type fingerprint mismatch: {row['declaration_name']}")
    prior = read(PIPELINE / "analysis_finish_time_module_status.json")
    require(prior["status"] == "PASS" and prior["coverage"]["accepted_files"] == 37
            and prior["coverage"]["accepted_declarations"] == 322,
            "previous publication baseline invalid")
    supply = read(PIPELINE / "model_processor_supply_module_manifest.json")
    divmod = read(PIPELINE / "div_mod_module_manifest.json")
    for name, manifest in (("Supply", supply), ("DivMod", divmod)):
        require(manifest["acceptance"] == "ACCEPTED_V06_FILE"
                and sha(PROJECT / manifest["production_file"])
                == manifest["production_source_sha256"],
                f"accepted {name} dependency stale")
    require(sha(WORK / "olean/Prosa/Model/Processor/Supply.olean")
            == supply["production_olean_sha256"], "reused Supply .olean changed")
    require(sha(WORK / "olean/Prosa/Util/Div_mod.olean")
            == sha(PRODUCER / "olean/Prosa/Util/Div_mod.olean"),
            "verified DivMod closure changed")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version"),
            "Lean toolchain changed")
    require(command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474",
            "Mathlib revision changed")
    require("9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                              "rocq", "--version"), "Rocq toolchain changed")
    tooling = read(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"], "exporter changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"], "importer changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "importer foundation changed")

    production = PROJECT / "Prosa/Analysis/Definitions/Sbf/Average.lean"
    olean = WORK / "olean/Prosa/Analysis/Definitions/Sbf/Average.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/AverageExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/AverageExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "stale Lean target/wrapper")
    lean_audit = (WORK / "lean_audit.log").read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit,
            "Lean proof-clean audit failed")
    for name in NAMES:
        full = MODULE + "." + name
        require(full in lean_audit, f"missing Lean elaborated type: {full}")
    require("'" + MODULE + ".arm_sbf' does not depend on any axioms" in lean_audit,
            "arm_sbf Lean axiom audit failed")
    match = re.search(r"'" + re.escape(MODULE)
                      + r"\.average_resource_model' depends on axioms: \[([^\]]*)\]",
                      lean_audit, re.S)
    require(match is not None and {x.strip() for x in match.group(1).split(",")}
            <= {"propext", "Classical.choice", "Quot.sound"},
            "average_resource_model has an unexpected Lean axiom")

    config_path = PROJECT / "Validation/tooling/analysis_sbf_average_export_config.json"
    config = read(config_path)
    metadata = read(WORK / "export_metadata.json")
    export = WORK / "Average.out"
    require(metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 0
            and len(metadata["normalization"]["body_projections"]) == 5
            and all(MODULE + "." + name in config["definition_targets"]
                    for name in NAMES), "compiled export/config invalid")
    imported = WORK / "ImportedAverage.v"
    imported_vo = WORK / "ImportedAverage.vo"
    require('Lean Import "Validation/.work/experiments/analysis_sbf_average/Average.out".'
            in imported.read_text() and export.stat().st_mtime_ns
            < imported_vo.stat().st_mtime_ns,
            "imported Rocq artifact does not bind current export")
    require("line 91989:" in (WORK / "import.log").read_text()
            and (WORK / "import_combined.log").stat().st_size > 0,
            "importer failure/recovery evidence missing")

    cert = PROJECT / "Validation/certificates/analysis/AverageCorrespondence.v"
    audit = PROJECT / "Validation/certificates/analysis/AverageAssumptionAudit.v"
    audit_config = PROJECT / "Validation/certificates/analysis/average_assumption_config.json"
    for path in (production, cert, audit):
        require(not any(x in path.read_text() for x in ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden placeholder/axiom: {path}")
    cert_text = cert.read_text()
    require(all("prosa.analysis.definitions.sbf.average." + name in cert_text
                and "ImportedAverage.Prosa_Analysis_Definitions_Sbf_Average_" + name
                in cert_text for name in NAMES)
            and "supply_during_correspondence" in cert_text
            and "dm_div_correspondence" in cert_text,
            "correspondence lacks official source/actual target composition")
    for path in (cert, audit):
        require(path.stat().st_mtime_ns < path.with_suffix(".vo").stat().st_mtime_ns,
                f"stale Rocq certificate: {path}")
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "audit policy changed")
    for name in ["average_bound", *NAMES]:
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
        "source_copy": copy, "source_vo": copy.with_suffix(".vo"),
        "source_type_inspection_vo": WORK / "AverageSourceInspection.vo",
        "target_type_inspection_vo": WORK / "AverageImportedInspection.vo",
        "compatibility_patch": patch,
        "production_source": production, "production_olean": olean,
        "wrapper_source": wrapper, "wrapper_olean": wrapper_olean,
        "divmod_interface_olean": WORK / "olean/Validation/fixtures/translation_order/DivModComputationInterface.olean",
        "supply_interface_olean": WORK / "olean/Validation/fixtures/translation_order/SupplyComputationInterface.olean",
        "lean_audit_log": WORK / "lean_audit.log",
        "export_config": config_path, "export_metadata": WORK / "export_metadata.json",
        "export": export, "imported_source": imported, "imported_vo": imported_vo,
        "certificate_source": cert, "certificate_vo": cert.with_suffix(".vo"),
        "audit_source": audit, "audit_vo": audit.with_suffix(".vo"),
        "audit_config": audit_config,
        "assumption_summary": WORK / "assumption_summary.json",
        "supply_reuse_evidence": WORK / "dependency_reuse_evidence.json",
    }
    for filename in ("SupplyBaseAdapter", "SupplyNatBoolOperations",
                     "SupplyIntervalOperations", "SupplyScheduleBaseAdapter",
                     "SupplyScheduleFiniteOperations", "SupplyScheduleOperations",
                     "SupplyCorrespondence", "NatSubCorrespondence",
                     "DivModCorrespondence"):
        artifacts[f"replayed_{filename}_source"] = WORK / f"certificates/{filename}.v"
        artifacts[f"replayed_{filename}_vo"] = WORK / f"certificates/{filename}.vo"
    hashes = {key + "_sha256": sha(path) for key, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_SBF_AVERAGE", "source_commit": PIN,
        "source_file": FILE, "source_file_sha256": official_sha,
        "source_compatibility": "Rocq 9.3 MathComp div import only; declaration text unchanged",
        "production_file": "Prosa/Analysis/Definitions/Sbf/Average.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": MODULE + "." + row["declaration_name"],
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": row["declaration_name"] + "_correspondence",
            "semantic_status": summary["certificates"][row["declaration_name"]]["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION"
        } for row in rows],
        "artifact_hashes": hashes,
        "tooling_manifest_sha256": sha(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {FILE: {
            "public_declarations": 2, "translated": 2, "proof_clean": 2,
            "certified": 2, "certified_without_prop_sprop_foundation": 0,
            "certified_with_prop_sprop_foundation": 2,
            "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**prior["coverage"], "accepted_files": 38,
                     "accepted_declarations": 324,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPELINE / "analysis_sbf_average_module_manifest.json"
    status_path = PIPELINE / "analysis_sbf_average_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "declarations": len(manifest["declarations"]),
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
