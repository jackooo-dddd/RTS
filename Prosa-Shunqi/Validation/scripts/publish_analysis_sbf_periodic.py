#!/usr/bin/env python3
"""Fail-closed whole-file publication for pinned periodic SBF definitions."""

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
WORK = PROJECT / "Validation/.work/experiments/analysis_sbf_periodic"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
FILE = "analysis/definitions/sbf/periodic.v"
MODULE = "Prosa.Analysis.Definitions.Sbf.Periodic"
NAMES = ["periodic_resource_model", "prm_sbf"]
PRODUCER = PROJECT / "Validation/.work/incremental/model_processor_supply/592b3619f31955d0c4b7b87798f4e43c45e879af7946b4a6e386c9d0c88bbb09"
REPLAY = ["SupplyBaseAdapter", "SupplyScheduleBaseAdapter",
          "SupplyScheduleFiniteOperations", "SupplyScheduleOperations",
          "SupplyNatBoolOperations", "SupplyIntervalOperations",
          "SupplyCorrespondence", "NatSubCorrespondence",
          "DivModCorrespondence"]


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
    selection = read(PIPELINE / "analysis_sbf_periodic_selection.json")
    require(selection["rank"] == 40 and selection["file_dag_ready"]
            and selection["source_file"] == FILE
            and selection["targets_in_source_order"] == NAMES,
            "selection/order/inventory mismatch")
    source = PROJECT / "Validation/.work/prosa-v06-414e667"
    require(command("git", "-C", str(source), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(source), "status", "--porcelain"),
            "authoritative source checkout not clean/pinned")
    official = source / FILE
    require(sha(official) == selection["source_sha256"], "source changed")
    copy = WORK / "source/analysis/definitions/sbf/periodic.v"
    require(copy.read_text() == official.read_text().replace(
        "Require Export prosa.model.processor.supply.\n",
        "Require Export prosa.model.processor.supply.\nFrom mathcomp Require Import div.\n", 1),
        "Rocq-9.3 compatibility copy changed a declaration")
    patch = PROJECT / "Validation/patches/prosa-v06-rocq93-analysis-sbf-periodic.patch"
    require(FILE in command("patch", "--dry-run", "--forward", "-p1", "-d",
                            str(source), "-i", str(patch)),
            "source patch does not apply to pinned source")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == FILE]
    require([r["declaration_name"] for r in rows] == NAMES,
            "public declaration inventory mismatch")
    type_evidence = read(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
                f"official elaborated type mismatch: {row['declaration_name']}")
    prior = read(PIPELINE / "analysis_sbf_average_module_status.json")
    require(prior["status"] == "PASS"
            and prior["coverage"]["accepted_files"] == 38
            and prior["coverage"]["accepted_declarations"] == 324,
            "previous publication baseline invalid")
    for label, filename in (("Supply", "model_processor_supply_module_manifest.json"),
                            ("DivMod", "div_mod_module_manifest.json")):
        manifest = read(PIPELINE / filename)
        require(manifest["acceptance"] == "ACCEPTED_V06_FILE"
                and sha(PROJECT / manifest["production_file"])
                == manifest["production_source_sha256"],
                f"accepted {label} dependency stale")
    supply = read(PIPELINE / "model_processor_supply_module_manifest.json")
    average = read(PIPELINE / "analysis_sbf_average_module_manifest.json")
    require(sha(WORK / "olean/Prosa/Model/Processor/Supply.olean")
            == supply["production_olean_sha256"], "reused Supply artifact changed")
    require(sha(WORK / "olean/Prosa/Util/Div_mod.olean")
            == sha(PRODUCER / "olean/Prosa/Util/Div_mod.olean"),
            "reused DivMod artifact changed")
    for name in ("SupplyComputationInterface", "DivModComputationInterface"):
        path = WORK / f"olean/Validation/fixtures/translation_order/{name}.olean"
        require(sha(path) == sha(PROJECT / f"Validation/.work/experiments/analysis_sbf_average/olean/Validation/fixtures/translation_order/{name}.olean"),
                f"reused {name} interface changed")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version"),
            "Lean version changed")
    require(command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474", "Mathlib changed")
    require("9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                              "rocq", "--version"), "Rocq version changed")
    tooling = read(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"], "exporter changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"], "importer changed")
    require(sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "importer foundation changed")
    production = PROJECT / "Prosa/Analysis/Definitions/Sbf/Periodic.lean"
    olean = WORK / "olean/Prosa/Analysis/Definitions/Sbf/Periodic.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/PeriodicExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/PeriodicExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "stale Lean compile/interface")
    lean_audit = (WORK / "lean_audit.log").read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit,
            "Lean proof-clean audit failed")
    for name in NAMES:
        require(MODULE + "." + name in lean_audit, f"missing type: {name}")
    require("'" + MODULE + ".prm_sbf' does not depend on any axioms" in lean_audit,
            "prm_sbf Lean proof-clean audit failed")
    match = re.search(r"'" + re.escape(MODULE)
                      + r"\.periodic_resource_model' depends on axioms: \[([^\]]*)\]",
                      lean_audit, re.S)
    require(match is not None and {s.strip() for s in match.group(1).split(",")}
            <= {"propext", "Classical.choice", "Quot.sound"},
            "periodic_resource_model unexpected Lean axiom")
    config_path = PROJECT / "Validation/tooling/analysis_sbf_periodic_export_config.json"
    config = read(config_path)
    metadata = read(WORK / "export_metadata.json")
    export = WORK / "Periodic.out"
    require(metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 0
            and len(metadata["normalization"]["body_projections"]) == 5
            and all(MODULE + "." + n in config["definition_targets"] for n in NAMES),
            "actual export/config invalid")
    imported = WORK / "ImportedPeriodic.v"
    imported_vo = WORK / "ImportedPeriodic.vo"
    require('Lean Import "Validation/.work/experiments/analysis_sbf_periodic/Periodic.out".'
            in imported.read_text() and export.stat().st_mtime_ns
            < imported_vo.stat().st_mtime_ns, "imported artifact stale")
    cert = PROJECT / "Validation/certificates/analysis/PeriodicCorrespondence.v"
    audit = PROJECT / "Validation/certificates/analysis/PeriodicAssumptionAudit.v"
    audit_config = PROJECT / "Validation/certificates/analysis/periodic_assumption_config.json"
    for path in (production, cert, audit):
        require(not any(x in path.read_text() for x in
                        ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden placeholder/axiom: {path}")
    cert_text = cert.read_text()
    require(all("prosa.analysis.definitions.sbf.periodic." + n in cert_text
                and "ImportedPeriodic.Prosa_Analysis_Definitions_Sbf_Periodic_" + n
                in cert_text for n in NAMES)
            and "supply_during_correspondence" in cert_text
            and "dm_div_correspondence" in cert_text,
            "proof does not compose real source/target lower-level relations")
    for path in (cert, audit):
        require(path.stat().st_mtime_ns < path.with_suffix(".vo").stat().st_mtime_ns,
                f"stale Rocq certificate/audit: {path}")
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "audit policy changed")
    for name in ("periodic_bound", *NAMES):
        record = summary["certificates"][name]
        require(record["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and record["prop_sprop_foundation"] ==
                ["PropSPropFoundation.interpret_strict"]
                and not record["semantic_premises"]
                and not record["statement_only_dependencies"]
                and not record["source_theorem_dependency"]
                and not record["target_theorem_dependency"]
                and not record["unexpected"],
                f"unclean assumption audit: {name}")
    require(not command("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")

    artifacts = {
        "source_copy": copy, "source_vo": copy.with_suffix(".vo"),
        "type_inspection_vo": WORK / "PeriodicTypeInspection.vo",
        "compatibility_patch": patch,
        "production_source": production, "production_olean": olean,
        "wrapper_source": wrapper, "wrapper_olean": wrapper_olean,
        "lean_audit_log": WORK / "lean_audit.log",
        "export_config": config_path, "export_metadata": WORK / "export_metadata.json",
        "export": export, "imported_source": imported, "imported_vo": imported_vo,
        "certificate_source": cert, "certificate_vo": cert.with_suffix(".vo"),
        "audit_source": audit, "audit_vo": audit.with_suffix(".vo"),
        "audit_config": audit_config,
        "assumption_summary": WORK / "assumption_summary.json",
        "supply_reuse_evidence": WORK / "dependency_reuse_evidence.json",
        "replay_script": PROJECT / "Validation/scripts/replay_nat_divmod_correspondence.py",
    }
    for filename in REPLAY:
        artifacts[f"replayed_{filename}_source"] = WORK / f"certificates/{filename}.v"
        artifacts[f"replayed_{filename}_vo"] = WORK / f"certificates/{filename}.vo"
    hashes = {key + "_sha256": sha(path) for key, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_SBF_PERIODIC", "source_commit": PIN,
        "source_file": FILE, "source_file_sha256": sha(official),
        "source_compatibility": "Rocq 9.3 MathComp div import only; declaration text unchanged",
        "production_file": "Prosa/Analysis/Definitions/Sbf/Periodic.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": r["qualified_name"],
            "lean_declaration": MODULE + "." + r["declaration_name"],
            "kind": r["kind"],
            "source_command_sha256": r["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[r["qualified_name"]]["sha256"],
            "semantic_certificate": r["declaration_name"] + "_correspondence",
            "semantic_status": summary["certificates"][r["declaration_name"]]["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION"
        } for r in rows],
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
        "coverage": {**prior["coverage"], "accepted_files": 39,
                     "accepted_declarations": 326,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPELINE / "analysis_sbf_periodic_module_manifest.json"
    status_path = PIPELINE / "analysis_sbf_periodic_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "declarations": len(manifest["declarations"]),
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
