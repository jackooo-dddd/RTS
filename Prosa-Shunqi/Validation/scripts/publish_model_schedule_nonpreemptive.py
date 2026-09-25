#!/usr/bin/env python3
"""Fail-closed publication of pinned v0.6 model/schedule/nonpreemptive.v."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
VALIDATION = PROJECT / "Validation"
PIPE = VALIDATION / "planning/v06_pipeline"
WORK = VALIDATION / ".work/experiments/model_schedule_nonpreemptive"
SOURCE = "model/schedule/nonpreemptive.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
MODULES = (
    "PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence",
    "NonpreemptiveBaseAdapter", "NonpreemptiveNatBoolOperations",
    "NonpreemptiveIntervalOperations", "NonpreemptiveScheduleOperations",
    "NonpreemptiveJobOperations", "NonpreemptiveCorrespondence",
    "NonpreemptiveScheduleCorrespondence", "NonpreemptiveExactTypeGuards",
    "NonpreemptiveAssumptionAudit",
)


def require(value: bool, message: str) -> None:
    if not value:
        raise SystemExit(f"NONPREEMPTIVE_PUBLICATION_REJECTED: {message}")


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = load(PIPE / "model_schedule_nonpreemptive_selection.json")
    baseline = load(PIPE / "model_schedule_edf_module_status.json")
    require(selection["source_commit"] == PIN and selection["source_file"] == SOURCE
            and selection["rank"] == 58 and selection["layer"] == 10
            and selection["file_dag_ready"]
            and selection["direct_internal_dependencies"] == ["behavior/all.v"]
            and selection["targets_in_source_order"] == ["nonpreemptive_schedule"]
            and selection["public_declaration_count"] == 1,
            "selection/DAG/inventory mismatch")
    require(baseline["status"] == "PASS"
            and baseline["coverage"]["accepted_files"] == 54
            and baseline["coverage"]["accepted_declarations"] == 389,
            "previous accepted state changed")

    pinned = VALIDATION / ".work/prosa-v06-414e667"
    official = pinned / SOURCE
    source = WORK / "source" / SOURCE
    source_vo = source.with_suffix(".vo")
    require(command("git", "-C", str(pinned), "rev-parse", "HEAD") == PIN
            and command("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}")
            == "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
            and not command("git", "-C", str(pinned), "status", "--porcelain",
                            "--untracked-files=all")
            and sha(official) == selection["source_sha256"] == sha(source)
            and sha(source_vo)
            and source_vo.stat().st_mtime_ns > source.stat().st_mtime_ns,
            "official source provenance/compile failed")
    source_audit = WORK / "source_type_audit.log"
    require("Error:" not in source_audit.read_text()
            and "@nonpreemptive_schedule" in source_audit.read_text(),
            "official elaborated type audit missing")
    with (VALIDATION / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    require(len(rows) == 1 and rows[0]["declaration_name"] == "nonpreemptive_schedule",
            "public inventory changed")
    row = rows[0]
    type_evidence = load(VALIDATION / "planning/v06_dependency/declaration_type_evidence.json")
    require(row["final_type_or_type_fingerprint"] ==
            "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
            "source elaborated type fingerprint changed")

    dependency = load(PIPE / "behavior_all_module_manifest.json")
    dependency_status = load(PIPE / "behavior_all_module_status.json")
    require(dependency["acceptance"] == "ACCEPTED_V06_FILE"
            and dependency_status["status"] == "PASS"
            and sha(PROJECT / dependency["production_file"])
            == dependency["production_source_sha256"]
            and sha(WORK / "olean/Prosa/Behavior/All.olean")
            == dependency["production_olean_sha256"],
            "accepted Behavior.All closure changed")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version")
            and command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                        "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in command("opam", "exec", "--switch=rocq93rc1",
                                 "--", "rocq", "--version"),
            "toolchain changed")
    tooling = load(VALIDATION / "tooling/tooling_manifest.json")
    require(sha(VALIDATION / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "tooling/foundation changed")

    production = PROJECT / "Prosa/Model/Schedule/Nonpreemptive.lean"
    olean = WORK / "olean/Prosa/Model/Schedule/Nonpreemptive.olean"
    lean_audit = WORK / "lean_audit.log"
    require(sha(olean) and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
            and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text())
            and "error:" not in lean_audit.read_text()
            and "sorryAx" not in lean_audit.read_text()
            and "'Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]" in lean_audit.read_text(),
            "Lean fresh compile/proof-clean failed")
    fixtures = (
        "NonpreemptiveComputationInterface", "ServiceComputationInterface",
        "ScheduleComputationInterface",
    )
    for name in fixtures:
        v = VALIDATION / f"fixtures/translation_order/{name}.lean"
        vo = WORK / f"olean/Validation/fixtures/translation_order/{name}.olean"
        require(sha(v) and sha(vo) and vo.stat().st_mtime_ns > v.stat().st_mtime_ns,
                f"kernel-guarded interface stale: {name}")

    config = VALIDATION / "tooling/model_schedule_nonpreemptive_guarded_export_config.json"
    export = WORK / "imported/NonpreemptiveGuarded.out"
    meta = load(WORK / "export_metadata.json")
    export_log = (WORK / "export_guarded.log").read_text()
    c = load(config)
    require(c["module"] == "Validation.fixtures.translation_order.NonpreemptiveComputationInterface"
            and "Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule" in c["targets"]
            and c["statement_only"] == [] and meta["statement_only_count"] == 0
            and meta["config_sha256"] == sha(config)
            and meta["output_sha256"] == sha(export)
            and len(c["normalization"]["body_projections"]) == 12
            and export_log.count("kernel_rfl_guard=true") == 12,
            "compiled artifact or 12 kernel body projections changed")
    imported = WORK / "imported"
    wrapper = imported / "ImportedNonpreemptive.v"
    imported_vo = imported / "ImportedNonpreemptive.vo"
    require(wrapper.read_text() ==
            'From LeanImport Require Import Lean.\nLean Import "NonpreemptiveGuarded.out".\n'
            and sha(imported_vo)
            and imported_vo.stat().st_mtime_ns > export.stat().st_mtime_ns
            and imported_vo.stat().st_mtime_ns > wrapper.stat().st_mtime_ns,
            "actual Lean export not freshly imported")
    adapter_meta = load(WORK / "certificates/nonpreemptive_base_adapter.json")
    replay_meta = load(WORK / "certificates/nonpreemptive_service_instantiation.json")
    require(adapter_meta["imported_artifact_sha256"] == sha(imported_vo)
            and adapter_meta["semantic_assumptions_added"] == []
            and replay_meta["imported_artifact_sha256"] == sha(imported_vo),
            "artifact-local adapters not bound to this import")
    controlled = VALIDATION / "certificates/model_schedule_nonpreemptive"
    compiled = WORK / "certificates"
    for name in MODULES:
        original = (controlled if name.startswith("Nonpreemptive") else
                    VALIDATION / "certificates/common") / f"{name}.v"
        copied = compiled / f"{name}.v"
        vo = compiled / f"{name}.vo"
        proof_text = copied.read_text()
        if name == "PropSPropFoundation":
            require(proof_text.count("Axiom interpret_strict :") == 1,
                    "approved Prop/SProp trust boundary changed")
            proof_text = proof_text.replace(
                "Axiom interpret_strict :", "Definition audited_interpret_strict_boundary :")
        require(sha(original) == sha(copied) and sha(vo)
                and vo.stat().st_mtime_ns > copied.stat().st_mtime_ns
                and not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", proof_text),
                f"certificate source/proof stale: {name}")
    for name, item in replay_meta["generated"].items():
        require(sha(PROJECT / item["source"]) == item["source_sha256"]
                and sha(PROJECT / item["output"]) == item["output_sha256"],
                f"replayed source proof drift: {name}")
    require(sha(controlled / "NonpreemptiveBaseAdapter.v") ==
            adapter_meta["output_sha256"], "generated base adapter drift")
    assumption_log = compiled / "NonpreemptiveAssumptionAudit.log"
    summary = load(compiled / "assumption_summary.json")
    require(sha(assumption_log) and summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == {"nonpreemptive_schedule"},
            "Print Assumptions output missing/truncated")
    item = summary["certificates"]["nonpreemptive_schedule"]
    require(item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
            and item["semantic_premises"] == []
            and item["statement_only_dependencies"] == []
            and item["unexpected"] == []
            and item["prop_sprop_foundation"] ==
            ["PropSPropFoundation.interpret_strict"]
            and not item["source_theorem_dependency"]
            and not item["target_theorem_dependency"],
            "semantic assumption gate failed")
    require(not command("git", "-C", str(ROOT), "status", "--porcelain", "--",
                        "Prosa-fei"), "historical workspace modified")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = VALIDATION / "imported/translation_order/nonpreemptive"
    require(not destination.exists(), "published artifact already exists")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".nonpreemptive.", dir=destination.parent))
    artifact_sources = {
        "export": export, "export_metadata": WORK / "export_metadata.json",
        "imported_v": wrapper, "imported_vo": imported_vo,
        "assumption_log": assumption_log,
        "assumption_summary": compiled / "assumption_summary.json",
        "source_type_audit": source_audit, "lean_audit": lean_audit,
        "export_log": WORK / "export_guarded.log",
        "adapter_metadata": WORK / "certificates/nonpreemptive_base_adapter.json",
        "replay_metadata": WORK / "certificates/nonpreemptive_service_instantiation.json",
    }
    for path in artifact_sources.values():
        shutil.copy2(path, stage / path.name)
    (stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(compiled / f"{name}{suffix}",
                         stage / "certificates" / f"{name}{suffix}")
    require(sha(stage / export.name) == sha(export)
            and sha(stage / imported_vo.name) == sha(imported_vo),
            "staging corrupted")
    stage.rename(destination)

    artifacts = {
        "official_source": official, "source_copy": source, "source_vo": source_vo,
        "production_source": production, "production_olean": olean,
        "export_config": config, "dependency_manifest": PIPE / "behavior_all_module_manifest.json",
        "assumption_config": controlled / "nonpreemptive_assumption_config.json",
    }
    artifacts.update({name: destination / path.name for name, path in artifact_sources.items()})
    for name in fixtures:
        artifacts[f"{name}_source"] = VALIDATION / f"fixtures/translation_order/{name}.lean"
        artifacts[f"{name}_olean"] = WORK / f"olean/Validation/fixtures/translation_order/{name}.olean"
    for name in MODULES:
        artifacts[f"{name}_v"] = controlled / f"{name}.v" if name.startswith("Nonpreemptive") else compiled / f"{name}.v"
        artifacts[f"{name}_vo"] = destination / "certificates" / f"{name}.vo"
    manifest = {
        "slice": "MODEL_SCHEDULE_NONPREEMPTIVE",
        "source_commit": PIN, "source_file": SOURCE,
        "source_file_sha256": sha(official),
        "source_compatibility": "byte-identical official source; no patch",
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule",
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": "nonpreemptive_schedule_correspondence",
            "semantic_status": item["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation": item["prop_sprop_foundation"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        }],
        "artifact_hashes": {key + "_sha256": sha(path) for key, path in artifacts.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT)) for key, path in artifacts.items()
                           if path.is_relative_to(PROJECT)},
        "tooling_manifest_sha256": sha(VALIDATION / "tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path = PIPE / "model_schedule_nonpreemptive_module_manifest.json"
    status_path = PIPE / "model_schedule_nonpreemptive_module_status.json"
    require(not manifest_path.exists() and not status_path.exists(),
            "formal machine publication already exists")
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {"public_declarations": 1, "translated": 1,
                              "proof_clean": 1, "certified": 0,
                              "certified_with_prop_sprop_foundation": 1,
                              "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**baseline["coverage"], "accepted_files": 55,
                     "accepted_declarations": 390},
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "accepted_files": 55,
                      "accepted_declarations": 390}, sort_keys=True))


if __name__ == "__main__":
    main()
