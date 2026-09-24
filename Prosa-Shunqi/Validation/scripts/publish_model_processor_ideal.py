#!/usr/bin/env python3
"""Fail-closed publication of pinned v0.6 model/processor/ideal.v."""

from __future__ import annotations

import csv
import hashlib
import json
import subprocess
from datetime import datetime, timedelta, timezone
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
PIPE = PROJECT / "Validation/planning/v06_pipeline"
WORK = PROJECT / "Validation/.work/experiments/model_processor_ideal"
PRODUCER = PROJECT / "Validation/.work/runs/behavior_all_finalize.djIKMA"
SOURCE = "model/processor/ideal.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
NAMES = ("processor_state", "ideal_is_idle")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selected = read(PIPE / "model_processor_ideal_selection.json")
    require(selected["source_commit"] == PIN and selected["rank"] == 48
            and selected["source_file"] == SOURCE and selected["file_dag_ready"]
            and selected["direct_internal_dependencies"] == ["behavior/all.v"]
            and selected["targets_in_source_order"] == list(NAMES),
            "selection/DAG mismatch")
    previous = read(PIPE / "model_job_properties_module_status.json")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 46
            and previous["coverage"]["accepted_declarations"] == 344,
            "published baseline changed")
    source_root = PROJECT / "Validation/.work/prosa-v06-414e667"
    official = source_root / SOURCE
    source_copy = WORK / "source" / SOURCE
    require(command("git", "-C", str(source_root), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(source_root), "status", "--porcelain")
            and sha(official) == selected["source_sha256"],
            "pinned source changed")
    original = official.read_text()
    old_proof = "    by move=> j s ?; rewrite /nat_of_bool; case: ifP => // ? /negP[]."
    require(original.count(old_proof) == 2, "unknown source proof shape")
    compatible = original.replace(old_proof, "    by case: ifP.", 1)
    compatible = compatible.replace(old_proof, "    by rewrite (negbTE H).", 1)
    require(source_copy.read_text() == compatible,
            "source compatibility patch changes declaration/statement/body")
    patch = PROJECT / "Validation/patches/prosa-v06-rocq93-model-processor-ideal.patch"
    require(sha(patch) ==
            "ae5f3f83ce8b213aa8c8cb2177de3003d45a1c40e96fff3ae2bb85cf4550f0a3",
            "compatibility patch changed")
    require(source_copy.stat().st_mtime_ns < source_copy.with_suffix(".vo").stat().st_mtime_ns,
            "stale Rocq source compile")

    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as f:
        rows = [row for row in csv.DictReader(f) if row["source_file"] == SOURCE]
    require([row["declaration_name"] for row in rows] == list(NAMES),
            "public declaration inventory mismatch")
    type_evidence = read(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
                "source elaborated type evidence changed")

    dependency_manifest = PIPE / "behavior_all_module_manifest.json"
    dependency = read(dependency_manifest)
    require(dependency["acceptance"] == "ACCEPTED_V06_FILE"
            and sha(PROJECT / dependency["production_file"]) ==
                dependency["production_source_sha256"]
            and sha(PRODUCER / "olean/Prosa/Behavior/All.olean") ==
                dependency["production_olean_sha256"],
            "accepted Behavior.All producer changed")
    for tree in ("Prosa", "Validation"):
        for item in (PRODUCER / "olean" / tree).rglob("*.olean"):
            require(sha(item) == sha(WORK / "olean" / item.relative_to(PRODUCER / "olean")),
                    f"Lean dependency closure differs: {item}")

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
            "export/import tooling changed")

    production = PROJECT / "Prosa/Model/Processor/Ideal.lean"
    olean = WORK / "olean/Prosa/Model/Processor/Ideal.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/IdealExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/IdealExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "stale production Lean artifact")
    lean_audit = (WORK / "lean_audit.log").read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit
            and all(f"'Prosa.Model.Processor.Ideal.{name}' depends on axioms: "
                    "[propext, Classical.choice, Quot.sound]" in lean_audit
                    for name in NAMES), "Lean proof/axiom audit failed")
    export_config = PROJECT / "Validation/tooling/model_processor_ideal_export_config.json"
    config = read(export_config)
    exported = WORK / "Ideal.out"
    metadata_path = WORK / "export_metadata.json"
    metadata = read(metadata_path)
    require(config["definition_targets"] ==
            ["Prosa.Model.Processor.Ideal." + name for name in NAMES]
            and metadata["config_sha256"] == sha(export_config)
            and metadata["output_sha256"] == sha(exported)
            and metadata["statement_only_count"] == 0
            and metadata["definition_target_count"] == 2,
            "actual-artifact export mismatch")
    imported = WORK / "imported/ImportedIdeal.v"
    imported_vo = imported.with_suffix(".vo")
    require('Lean Import "Validation/.work/experiments/model_processor_ideal/Ideal.out".'
            in imported.read_text()
            and exported.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "stale/wrong imported Rocq artifact")

    cert_dir = PROJECT / "Validation/certificates/model_processor"
    cert_names = ("IdealBaseAdapter.v", "IdealCorrespondence.v",
                  "IdealExactTypeGuards.v", "IdealAssumptionAudit.v")
    for path in (production, *(cert_dir / name for name in cert_names)):
        require(not any(token in path.read_text() for token in
                        ("sorry", "Admitted", "admit.", "Axiom ", "unsafe ")),
                f"forbidden escape: {path}")
        if path.suffix == ".v":
            require(path.stat().st_mtime_ns < path.with_suffix(".vo").stat().st_mtime_ns,
                    f"stale certificate compile: {path}")
    adapter_meta = read(WORK / "base_adapter_metadata.json")
    require(adapter_meta["imported_module"] == "ImportedIdeal"
            and adapter_meta["imported_artifact_sha256"] == sha(exported)
            and adapter_meta["output_sha256"] == sha(cert_dir / "IdealBaseAdapter.v")
            and adapter_meta["template_sha256"] ==
                sha(PROJECT / "Validation/templates/ArtifactBoolListAdapter.v.tpl")
            and adapter_meta["semantic_assumptions_added"] == [],
            "artifact-local adapter provenance mismatch")
    corr_text = (cert_dir / "IdealCorrespondence.v").read_text()
    require(all("ImportedIdeal.Prosa_Model_Processor_Ideal_" + name in corr_text
                and "prosa.model.processor.ideal." + name in corr_text
                for name in NAMES)
            and all(name in corr_text for name in
                    ("ideal_scheduled_on_correspondence", "ideal_supply_on_correspondence",
                     "ideal_service_on_correspondence", "ideal_supply_law_correspondence",
                     "ideal_service_rule_correspondence")),
            "incomplete full class correspondence")
    guard_log = (WORK / "exact_type_guards.log").read_text()
    require(all("Prosa_Model_Processor_Ideal_" + name in guard_log
                and name in guard_log for name in NAMES),
            "missing exact-type guards")
    audit_config = cert_dir / "ideal_assumption_config.json"
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "audit policy changed")
    for key, expected in (("processor_state", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"),
                          ("ideal_is_idle", "CERTIFIED")):
        record = summary["certificates"][key]
        require(record["status"] == expected and not record["semantic_premises"]
                and not record["statement_only_dependencies"]
                and not record["source_theorem_dependency"]
                and not record["target_theorem_dependency"]
                and not record["unexpected"], f"assumption gate failed: {key}")
    require(all(not record["unexpected"] and not record["semantic_premises"]
                for record in summary["certificates"].values()),
            "operation-level assumption audit failed")
    require(not command("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")

    artifacts = {
        "official_source": official, "compatibility_source": source_copy,
        "compatibility_patch": patch, "source_vo": source_copy.with_suffix(".vo"),
        "production_source": production, "production_olean": olean,
        "export_wrapper": wrapper, "export_wrapper_olean": wrapper_olean,
        "export_config": export_config, "export_metadata": metadata_path,
        "export": exported, "imported_source": imported, "imported_vo": imported_vo,
        "lean_audit": WORK / "lean_audit.log",
        "exact_type_log": WORK / "exact_type_guards.log",
        "assumption_log": WORK / "assumptions.log",
        "assumption_summary": WORK / "assumption_summary.json",
        "assumption_config": audit_config,
        "adapter_metadata": WORK / "base_adapter_metadata.json",
        "adapter_template": PROJECT / "Validation/templates/ArtifactBoolListAdapter.v.tpl",
        "behavior_all_manifest": dependency_manifest,
    }
    for name in cert_names:
        artifacts[name] = cert_dir / name
        artifacts[name.replace(".v", ".vo")] = (cert_dir / name).with_suffix(".vo")
    hashes = {name + "_sha256": sha(path) for name, path in artifacts.items()}
    manifest = {
        "slice": "MODEL_PROCESSOR_IDEAL", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": sha(official),
        "source_compatibility": "two proof-script-only Rocq 9.3 obligation changes; public commands/types/bodies unchanged",
        "production_file": "Prosa/Model/Processor/Ideal.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Model.Processor.Ideal." + name,
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": ("ideal_processor_state_correspondence" if name == "processor_state"
                                     else "ideal_is_idle_correspondence"),
            "semantic_status": summary["certificates"][name]["status"],
            "input_relations": (["IdealOptionRel", "IdealBoolRel", "SubNatRel", "PropSPropRel"]
                                if name == "processor_state" else
                                ["IdealScheduleRel", "IdealOptionRel", "SubNatRel", "IdealBoolRel"]),
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": summary["certificates"][name]["prop_sprop_foundation"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION",
        } for name, row in zip(NAMES, rows)],
        "artifact_hashes": hashes,
        "tooling_manifest_sha256": sha(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path = PIPE / "model_processor_ideal_module_manifest.json"
    status_path = PIPE / "model_processor_ideal_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {"public_declarations": 2, "translated": 2,
                              "proof_clean": 2, "certified": 2,
                              "certified_with_prop_sprop_foundation": 1,
                              "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**previous["coverage"], "accepted_files": 47,
                     "accepted_declarations": 346,
                     "translated_but_not_certified": 0},
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
