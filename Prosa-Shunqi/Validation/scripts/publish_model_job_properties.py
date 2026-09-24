#!/usr/bin/env python3
"""Fail-closed publication of pinned v0.6 model/job/properties.v."""

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
PIPE = PROJECT / "Validation/planning/v06_pipeline"
WORK = PROJECT / "Validation/.work/experiments/model_job_properties"
PRODUCER = PROJECT / "Validation/.work/runs/behavior_all_finalize.djIKMA"
SOURCE = "model/job/properties.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
NAMES = ("job_cost_positive", "arrivals_have_positive_job_costs")


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selected = read(PIPE / "model_job_properties_selection.json")
    require(selected["rank"] == 47 and selected["source_file"] == SOURCE
            and selected["file_dag_ready"]
            and selected["direct_internal_dependencies"] == ["behavior/all.v"]
            and selected["targets_in_source_order"] == list(NAMES),
            "selection/DAG mismatch")
    source_root = PROJECT / "Validation/.work/prosa-v06-414e667"
    official = source_root / SOURCE
    source_copy = WORK / "source" / SOURCE
    require(command("git", "-C", str(source_root), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(source_root), "status", "--porcelain")
            and sha(official) == selected["source_sha256"] == sha(source_copy),
            "official source mismatch")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as f:
        rows = [r for r in csv.DictReader(f) if r["source_file"] == SOURCE]
    require([r["declaration_name"] for r in rows] == list(NAMES)
            and all(r["kind"] == "Definition" for r in rows),
            "public declaration inventory mismatch")
    evidence = read(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + evidence[row["qualified_name"]]["sha256"],
                f"source elaborated type mismatch: {row['declaration_name']}")
    previous = read(PIPE / "analysis_transform_swap_module_status.json")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 45
            and previous["coverage"]["accepted_declarations"] == 342,
            "published baseline changed")
    accepted_all = read(PIPE / "behavior_all_module_manifest.json")
    require(accepted_all["acceptance"] == "ACCEPTED_V06_FILE"
            and accepted_all["source_commit"] == PIN
            and sha(PROJECT / accepted_all["production_file"]) ==
                accepted_all["production_source_sha256"]
            and sha(PRODUCER / "olean/Prosa/Behavior/All.olean") ==
                accepted_all["production_olean_sha256"],
            "Behavior.All producer invalidated")
    for tree in ("Prosa", "Validation"):
        for dependency in (PRODUCER / "olean" / tree).rglob("*.olean"):
            relative = dependency.relative_to(PRODUCER / "olean")
            require(sha(dependency) == sha(WORK / "olean" / relative),
                    f"accepted Lean dependency changed: {relative}")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version")
            and command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                        "rev-parse", "HEAD") ==
                "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                                 "rocq", "--version"), "toolchain mismatch")
    tooling = read(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "tooling changed")
    production = PROJECT / "Prosa/Model/Job/Properties.lean"
    olean = WORK / "olean/Prosa/Model/Job/Properties.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/JobPropertiesExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/JobPropertiesExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "stale Lean snapshot")
    audit_text = (WORK / "lean_audit.log").read_text()
    require("error:" not in audit_text and "sorryAx" not in audit_text
            and "'Prosa.Model.Job.Properties.job_cost_positive' does not depend on any axioms"
                in audit_text, "Lean computation/axiom audit failed")
    match = re.search(
        r"'Prosa\.Model\.Job\.Properties\.arrivals_have_positive_job_costs' "
        r"depends on axioms: \[([^\]]*)\]", audit_text)
    require(match is not None and
            {x.strip() for x in match.group(1).split(",")}
            <= {"propext", "Classical.choice", "Quot.sound"},
            "Lean Prop-definition axiom audit failed")
    config_path = PROJECT / "Validation/tooling/model_job_properties_export_config.json"
    config = read(config_path)
    export = WORK / "JobProperties.out"
    metadata = read(WORK / "export_metadata.json")
    require(config["module"] ==
            "Validation.fixtures.translation_order.JobPropertiesExportInterface"
            and config["definition_targets"] ==
                ["Prosa.Model.Job.Properties." + n for n in NAMES]
            and metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 0,
            "actual Lean export/config mismatch")
    imported = WORK / "imported/ImportedJobProperties.v"
    imported_vo = WORK / "imported/ImportedJobProperties.vo"
    require('Lean Import "Validation/.work/experiments/model_job_properties/JobProperties.out".'
            in imported.read_text()
            and export.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "stale/wrong Rocq import")
    adapter = WORK / "certificates/JobPropertiesBaseAdapter.v"
    adapter_meta = read(WORK / "certificates/base_adapter_metadata.json")
    require(adapter_meta["imported_module"] == "ImportedJobProperties"
            and adapter_meta["imported_artifact_sha256"] == sha(export)
            and adapter_meta["template_sha256"] ==
                sha(PROJECT / "Validation/templates/ArtifactBoolListAdapter.v.tpl")
            and adapter_meta["output_sha256"] == sha(adapter)
            and adapter_meta["semantic_assumptions_added"] == [],
            "generated artifact adapter provenance mismatch")
    cert_dir = PROJECT / "Validation/certificates/model_job"
    cert_files = ("JobPropertiesOperations.v", "JobPropertiesCorrespondence.v",
                  "JobPropertiesExactTypeGuards.v", "JobPropertiesAssumptionAudit.v")
    for path in (production, adapter, *(cert_dir / name for name in cert_files)):
        require(not any(token in path.read_text() for token in
                        ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden escape: {path}")
    correspondence = (cert_dir / "JobPropertiesCorrespondence.v").read_text()
    require(all("ImportedJobProperties.Prosa_Model_Job_Properties_" + n
                in correspondence and "prosa.model.job.properties." + n
                in correspondence for n in NAMES)
            and "jp_arrives_in_related" in correspondence
            and "job_cost_positive_correspondence" in correspondence,
            "correspondence does not structurally bind actual declarations")
    for path in (adapter, *(cert_dir / name for name in cert_files)):
        copy = WORK / "certificates" / path.name
        require(sha(path) == sha(copy)
                and copy.stat().st_mtime_ns < copy.with_suffix(".vo").stat().st_mtime_ns,
                f"stale certificate: {path.name}")
    guard_log = (WORK / "exact_type_guards.log").read_text()
    require(all("@" + n in guard_log
                and "Prosa_Model_Job_Properties_" + n in guard_log
                for n in NAMES), "exact type guards missing")
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "audit policy mismatch")
    for key in ("adapter_membership", "arrives_in_dependency", *NAMES):
        rec = summary["certificates"][key]
        require(rec["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and not rec["semantic_premises"]
                and not rec["statement_only_dependencies"]
                and not rec["source_theorem_dependency"]
                and not rec["target_theorem_dependency"]
                and not rec["unexpected"], f"assumption audit failed: {key}")
    require(not command("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")
    artifacts = {
        "official_source": official, "source_copy": source_copy,
        "source_vo": source_copy.with_suffix(".vo"),
        "production_source": production, "production_olean": olean,
        "export_wrapper": wrapper, "export_wrapper_olean": wrapper_olean,
        "lean_audit": WORK / "lean_audit.log", "export_config": config_path,
        "export_metadata": WORK / "export_metadata.json", "export": export,
        "imported_source": imported, "imported_vo": imported_vo,
        "imported_audit": WORK / "imported_audit.log",
        "adapter": adapter, "adapter_vo": adapter.with_suffix(".vo"),
        "adapter_metadata": WORK / "certificates/base_adapter_metadata.json",
        "adapter_template": PROJECT / "Validation/templates/ArtifactBoolListAdapter.v.tpl",
        "exact_type_log": WORK / "exact_type_guards.log",
        "assumption_log": WORK / "assumption_audit.log",
        "assumption_summary": WORK / "assumption_summary.json",
        "assumption_config": cert_dir / "job_properties_assumption_config.json",
        "behavior_all_manifest": PIPE / "behavior_all_module_manifest.json",
    }
    for name in cert_files:
        artifacts[name] = cert_dir / name
        artifacts[name.replace(".v", ".vo")] = WORK / "certificates" / name.replace(".v", ".vo")
    hashes = {key + "_sha256": sha(path) for key, path in artifacts.items()}
    manifest = {
        "slice": "MODEL_JOB_PROPERTIES", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": sha(official),
        "source_compatibility": "byte-identical official source; no patch",
        "production_file": "Prosa/Model/Job/Properties.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Model.Job.Properties." + name,
            "kind": "Definition", "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": name + "_correspondence",
            "semantic_status": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
            "input_relations": ["JpJobCostRel", "JpArrivalSequenceRel",
                                "SubNatRel", "JpBoolRel", "PropSPropRel"],
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
        "per_file": {SOURCE: {"public_declarations": 2, "translated": 2,
                              "proof_clean": 2, "certified": 2,
                              "certified_with_prop_sprop_foundation": 2,
                              "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**previous["coverage"], "accepted_files": 46,
                     "accepted_declarations": 344,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPE / "model_job_properties_module_manifest.json"
    status_path = PIPE / "model_job_properties_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
