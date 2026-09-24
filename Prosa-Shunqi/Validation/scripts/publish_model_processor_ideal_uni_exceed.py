#!/usr/bin/env python3
"""Fail-closed publication for pinned v0.6 model/processor/ideal_uni_exceed.v."""

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
WORK = PROJECT / "Validation/.work/experiments/model_processor_ideal_uni_exceed"
PRODUCER = PROJECT / "Validation/.work/runs/behavior_all_finalize.djIKMA"
SOURCE = "model/processor/ideal_uni_exceed.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
NAMES = (
    "exceedance_processor_state", "exceedance_processor_state_eqdef",
    "eqn_exceedance_processor_state", "exceedance_scheduled_on",
    "exceedance_supply_on", "exceedance_service_on", "exceedance_proc_state",
)
CERTS = (
    "iue_target_roundtrip", "iue_eqdef_correspondence",
    "iue_eqn_statement_correspondence", "iue_scheduled_on_correspondence",
    "iue_supply_on_correspondence", "iue_service_on_correspondence",
    "iue_processor_state_correspondence",
)


def require(ok: bool, msg: str) -> None:
    if not ok:
        raise SystemExit(msg)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def cmd(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read(PIPE / "model_processor_ideal_uni_exceed_selection.json")
    require(selection["source_commit"] == PIN and selection["rank"] == 49
            and selection["source_file"] == SOURCE and selection["file_dag_ready"]
            and selection["direct_internal_dependencies"] == ["behavior/all.v"]
            and selection["targets_in_source_order"] == list(NAMES),
            "selection/DAG mismatch")
    previous = read(PIPE / "model_processor_ideal_module_status.json")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 47
            and previous["coverage"]["accepted_declarations"] == 346,
            "published baseline changed")

    source_root = PROJECT / "Validation/.work/prosa-v06-414e667"
    official = source_root / SOURCE
    source_copy = WORK / "source" / SOURCE
    require(cmd("git", "-C", str(source_root), "rev-parse", "HEAD") == PIN
            and not cmd("git", "-C", str(source_root), "status", "--porcelain")
            and sha(official) == selection["source_sha256"], "pinned source changed")
    old = "    by move => j [] // s [] /=; case: eqP; lia."
    require(official.read_text().count(old) == 2, "unknown source proof shape")
    compatible = official.read_text().replace(
        old, "    by case: s => [x|x|] //=; case: eqP; lia.", 1
    ).replace(old, "    by move: H; case: s => [x|x|] //=; case: eqP; lia.", 1)
    require(source_copy.read_text() == compatible,
            "compatibility copy changes declaration/statement/computation")
    patch = PROJECT / "Validation/patches/prosa-v06-rocq93-model-processor-ideal-uni-exceed.patch"
    require(sha(patch) ==
            "179425b3910319f5b7bacffa2a65478ba9cf91301bc0fac4772d6dcd1e9810ea",
            "compatibility patch changed")
    require(source_copy.stat().st_mtime_ns < source_copy.with_suffix(".vo").stat().st_mtime_ns,
            "stale source Rocq compile")

    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as f:
        rows = [row for row in csv.DictReader(f) if row["source_file"] == SOURCE]
    require([row["declaration_name"] for row in rows] == list(NAMES),
            "source declaration inventory mismatch")
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

    require("Lean (version 4.33.1" in cmd("lake", "env", "lean", "--version")
            and cmd("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD") ==
                "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in cmd("opam", "exec", "--switch=rocq93rc1", "--",
                              "rocq", "--version"), "toolchain mismatch")
    tooling = read(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Model/Processor/IdealUniExceed.lean"
    olean = WORK / "olean/Prosa/Model/Processor/IdealUniExceed.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/IdealUniExceedExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/IdealUniExceedExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "stale production Lean artifact")
    lean_audit = (WORK / "lean_audit.log").read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit,
            "Lean proof/axiom audit failed")
    expected_axioms = {
        "exceedance_processor_state_eqdef": "[propext]",
        "eqn_exceedance_processor_state": "[propext]",
        "exceedance_proc_state": "[propext, Classical.choice, Quot.sound]",
    }
    for name, axioms in expected_axioms.items():
        require(f"'Prosa.Model.Processor.IdealUniExceed.{name}' depends on axioms: {axioms}"
                in lean_audit, f"unreviewed Lean axiom: {name}")
    for name in ("exceedance_scheduled_on", "exceedance_supply_on", "exceedance_service_on"):
        require(f"'Prosa.Model.Processor.IdealUniExceed.{name}' does not depend on any axioms"
                in lean_audit, f"unreviewed Lean axiom: {name}")

    export_config = PROJECT / "Validation/tooling/model_processor_ideal_uni_exceed_export_config.json"
    config = read(export_config)
    exported = WORK / "IdealUniExceed.out"
    metadata = read(WORK / "export_metadata.json")
    require(config["definition_targets"] ==
            ["Prosa.Model.Processor.IdealUniExceed." + name for name in NAMES]
            and metadata["config_sha256"] == sha(export_config)
            and metadata["output_sha256"] == sha(exported)
            and metadata["statement_only_count"] == 0
            and metadata["definition_target_count"] == 7,
            "actual-artifact export mismatch")
    imported = WORK / "imported/ImportedIdealUniExceed.v"
    imported_vo = imported.with_suffix(".vo")
    require('Lean Import "Validation/.work/experiments/model_processor_ideal_uni_exceed/IdealUniExceed.out".'
            in imported.read_text()
            and exported.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "stale/wrong imported Rocq artifact")

    cert_dir = PROJECT / "Validation/certificates/model_processor"
    cert_names = ("IdealUniExceedBaseAdapter.v", "IdealUniExceedSourceOperations.v",
                  "IdealUniExceedCorrespondence.v", "IdealUniExceedExactTypeGuards.v",
                  "IdealUniExceedAssumptionAudit.v")
    for path in (production, *(cert_dir / name for name in cert_names)):
        require(not any(token in path.read_text() for token in
                        ("sorry", "Admitted", "admit.", "Axiom ", "unsafe ")),
                f"forbidden escape: {path}")
        if path.suffix == ".v":
            require(path.stat().st_mtime_ns < path.with_suffix(".vo").stat().st_mtime_ns,
                    f"stale certificate compile: {path}")
    adapter_meta = read(WORK / "base_adapter_metadata.json")
    require(adapter_meta["imported_module"] == "ImportedIdealUniExceed"
            and adapter_meta["imported_artifact_sha256"] == sha(exported)
            and adapter_meta["output_sha256"] == sha(cert_dir / "IdealUniExceedBaseAdapter.v")
            and adapter_meta["template_sha256"] ==
                sha(PROJECT / "Validation/templates/ArtifactBoolListAdapter.v.tpl")
            and adapter_meta["semantic_assumptions_added"] == [],
            "artifact-local adapter provenance mismatch")
    corr = (cert_dir / "IdealUniExceedCorrespondence.v").read_text()
    require(all(name in corr for name in CERTS)
            and "ImportedIdealUniExceed.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state"
                in corr
            and "prosa.model.processor.ideal_uni_exceed.exceedance_proc_state" in corr,
            "incomplete instance correspondence")
    guard_log = (WORK / "guards.log").read_text()
    require(all("Prosa_Model_Processor_IdealUniExceed_" + name in guard_log
                and name in guard_log for name in NAMES), "missing exact-type guards")
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(NAMES), "assumption audit incomplete")
    for name in NAMES:
        rec = summary["certificates"][name]
        expected = ("CERTIFIED" if name in
                    ("exceedance_processor_state", "exceedance_supply_on")
                    else "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")
        require(rec["certificate"] == CERTS[NAMES.index(name)]
                and rec["status"] == expected
                and not rec["semantic_premises"]
                and not rec["statement_only_dependencies"]
                and not rec["source_theorem_dependency"]
                and not rec["target_theorem_dependency"]
                and not rec["unexpected"], f"assumption gate failed: {name}")
    require(not cmd("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")

    artifacts = {
        "official_source": official, "compatibility_source": source_copy,
        "compatibility_patch": patch, "source_vo": source_copy.with_suffix(".vo"),
        "production_source": production, "production_olean": olean,
        "export_wrapper": wrapper, "export_wrapper_olean": wrapper_olean,
        "export_config": export_config, "export_metadata": WORK / "export_metadata.json",
        "export": exported, "imported_source": imported, "imported_vo": imported_vo,
        "lean_audit": WORK / "lean_audit.log", "exact_type_log": WORK / "guards.log",
        "assumption_log": WORK / "assumptions.log",
        "assumption_summary": WORK / "assumption_summary.json",
        "assumption_config": cert_dir / "ideal_uni_exceed_assumption_config.json",
        "adapter_metadata": WORK / "base_adapter_metadata.json",
        "adapter_template": PROJECT / "Validation/templates/ArtifactBoolListAdapter.v.tpl",
        "behavior_all_manifest": dependency_manifest,
    }
    for name in cert_names:
        artifacts[name] = cert_dir / name
        artifacts[name.replace(".v", ".vo")] = (cert_dir / name).with_suffix(".vo")
    hashes = {name + "_sha256": sha(path) for name, path in artifacts.items()}
    manifest = {
        "slice": "MODEL_PROCESSOR_IDEAL_UNI_EXCEED", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": sha(official),
        "source_compatibility": "two proof-script-only Rocq 9.3 obligation changes; public types/bodies unchanged",
        "production_file": "Prosa/Model/Processor/IdealUniExceed.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Model.Processor.IdealUniExceed." + name,
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": CERTS[index],
            "semantic_status": summary["certificates"][name]["status"],
            "input_relations": ["IueRel", "IueBoolRel", "SubNatRel", "PropSPropRel"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": summary["certificates"][name]["prop_sprop_foundation"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION",
        } for index, (name, row) in enumerate(zip(NAMES, rows))],
        "artifact_hashes": hashes,
        "tooling_manifest_sha256": sha(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path = PIPE / "model_processor_ideal_uni_exceed_module_manifest.json"
    status_path = PIPE / "model_processor_ideal_uni_exceed_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {"public_declarations": 7, "translated": 7,
                              "proof_clean": 7, "certified": 7,
                              "certified_with_prop_sprop_foundation": 5,
                              "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**previous["coverage"], "accepted_files": 48,
                     "accepted_declarations": 353,
                     "translated_but_not_certified": 0},
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
