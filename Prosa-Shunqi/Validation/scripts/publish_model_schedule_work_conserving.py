#!/usr/bin/env python3
"""Fail-closed publication for pinned v0.6 model/schedule/work_conserving.v."""

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
V = PROJECT / "Validation"
PIPE = V / "planning/v06_pipeline"
WORK = V / ".work/experiments/model_schedule_work_conserving"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE = "model/schedule/work_conserving.v"
NAMES = ("work_conserving", "jobs_backlogged_at")
MODULES = ("PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence",
           "ReadyBaseAdapter", "ReadyNatBoolOperations", "ReadyIntervalOperations",
           "ReadyScheduleOperations", "ReadyJobOperations", "ReadyServiceCorrespondence",
           "ReadyArrivalBaseAdapter", "ReadyArrivalOperations",
           "ReadyArrivalCorrespondence", "ReadyCorrespondence",
           "WorkConservingCorrespondence", "WorkConservingExactTypeGuards",
           "WorkConservingAssumptionAudit")


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise SystemExit("WORK_CONSERVING_PUBLICATION_REJECTED: " + reason)


def sha(path: Path) -> str:
    need(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def output(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read(PIPE / "model_schedule_work_conserving_selection.json")
    baseline = read(PIPE / "model_schedule_scheduled_module_status.json")
    need(selection["source_commit"] == PIN and selection["source_file"] == SOURCE
         and selection["rank"] == 60 and selection["layer"] == 10
         and selection["file_dag_ready"]
         and selection["direct_internal_dependencies"] == ["behavior/all.v"]
         and selection["targets_in_source_order"] == list(NAMES)
         and selection["public_declaration_count"] == 2, "selection/DAG mismatch")
    need(baseline["status"] == "PASS"
         and baseline["coverage"]["accepted_files"] == 56
         and baseline["coverage"]["accepted_declarations"] == 393,
         "previous accepted state changed")
    pinned = V / ".work/prosa-v06-414e667"
    official = pinned / SOURCE
    copied = WORK / "source" / SOURCE
    source_vo = copied.with_suffix(".vo")
    need(output("git", "-C", str(pinned), "rev-parse", "HEAD") == PIN
         and output("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}")
         == "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
         and not output("git", "-C", str(pinned), "status", "--porcelain",
                        "--untracked-files=all")
         and sha(official) == sha(copied) == selection["source_sha256"]
         and sha(source_vo) and source_vo.stat().st_mtime_ns > copied.stat().st_mtime_ns,
         "official source provenance/compile invalid")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    need([r["declaration_name"] for r in rows] == list(NAMES),
         "public declaration inventory changed")
    type_evidence = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        need(row["final_type_or_type_fingerprint"] ==
             "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
             f"official elaborated type changed: {row['declaration_name']}")
    source_audit = WORK / "source_type_audit.log"
    need("Error:" not in source_audit.read_text()
         and all("@" + name in source_audit.read_text() for name in NAMES),
         "official Check/Print type evidence missing")
    dep = read(PIPE / "behavior_all_module_manifest.json")
    dep_status = read(PIPE / "behavior_all_module_status.json")
    need(dep["acceptance"] == "ACCEPTED_V06_FILE" and dep_status["status"] == "PASS"
         and sha(PROJECT / dep["production_file"]) == dep["production_source_sha256"]
         and sha(WORK / "olean/Prosa/Behavior/All.olean")
         == dep["production_olean_sha256"], "accepted dependency changed")
    need("Lean (version 4.33.1" in output("lake", "env", "lean", "--version")
         and output("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD")
         == "0df444a360eaa60ab8c11dca51a86af692955474"
         and "9.3" in output("opam", "exec", "--switch=rocq93rc1", "--",
                             "rocq", "--version"), "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    need(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
         == tooling["lean4export"]["expected_binary_sha256"]
         and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
         == tooling["rocq_lean_import"]["expected_plugin_sha256"]
         and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo")
         == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
         "export/import foundation changed")

    production = PROJECT / "Prosa/Model/Schedule/WorkConserving.lean"
    olean = WORK / "olean/Prosa/Model/Schedule/WorkConserving.olean"
    lean_audit = WORK / "lean_audit.log"
    need(sha(production) and sha(olean)
         and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
         and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text())
         and "error:" not in lean_audit.read_text()
         and "sorryAx" not in lean_audit.read_text()
         and all("'Prosa.Model.Schedule.WorkConserving." + name +
                 "' depends on axioms: [propext, Classical.choice, Quot.sound]"
                 in lean_audit.read_text() for name in NAMES),
         "Lean build/type/proof-clean failed")
    fixtures = ("Schedule", "Service", "Bigcat", "Ready", "WorkConserving")
    for name in fixtures:
        v = V / f"fixtures/translation_order/{name}ComputationInterface.lean"
        vo = WORK / f"olean/Validation/fixtures/translation_order/{name}ComputationInterface.olean"
        need(sha(v) and sha(vo) and vo.stat().st_mtime_ns > v.stat().st_mtime_ns,
             f"kernel computation fixture stale: {name}")
    config = V / "tooling/model_schedule_work_conserving_export_config.json"
    cfg = read(config)
    export = WORK / "imported/WorkConserving.out"
    meta = read(WORK / "export_metadata.json")
    export_log = WORK / "imported/export.log"
    need(cfg["module"] == "Validation.fixtures.translation_order.WorkConservingComputationInterface"
         and cfg["targets"][:2] == [f"Prosa.Model.Schedule.WorkConserving.{x}" for x in NAMES]
         and cfg["statement_only"] == []
         and meta["statement_only_count"] == 0
         and meta["config_sha256"] == sha(config)
         and meta["output_sha256"] == sha(export)
         and len(cfg["normalization"]["body_projections"]) == 18
         and export_log.read_text().count("kernel_rfl_guard=true") == 18,
         "actual compiled export or 18 kernel projections changed")
    imported = WORK / "imported"
    wrapper = imported / "ImportedWorkConserving.v"
    imported_vo = imported / "ImportedWorkConserving.vo"
    need(wrapper.read_text() ==
         'From LeanImport Require Import Lean.\nLean Import "WorkConserving.out".\n'
         and sha(imported_vo)
         and imported_vo.stat().st_mtime_ns > export.stat().st_mtime_ns
         and imported_vo.stat().st_mtime_ns > wrapper.stat().st_mtime_ns,
         "fresh Rocq import missing/stale")
    cert = WORK / "certificates"
    ready_meta = read(cert / "work_conserving_ready_instantiation.json")
    arrival_meta = read(cert / "work_conserving_arrival_instantiation.json")
    replay = V / "certificates/model_schedule_work_conserving/replay_dependencies.py"
    need(sha(replay)
         and ready_meta["imported_artifact_sha256"] == sha(imported_vo)
         and arrival_meta["imported_artifact_sha256"] == sha(imported_vo),
         "generated operation DAG not bound to current import")
    for name, item in ready_meta["generated"].items():
        need(sha(V / "certificates/behavior_ready" / f"{name}.v") ==
             item["source_sha256"]
             and sha(cert / f"{name}.v") == item["output_sha256"],
             f"replayed Ready proof changed: {name}")
    for item in arrival_meta["generated"].values():
        source = Path(item["source"])
        target = Path(item["output"])
        if not source.is_absolute():
            source = PROJECT / source
        if not target.is_absolute():
            target = PROJECT / target
        need(sha(source) == item["source_sha256"]
             and sha(target) == item["output_sha256"],
             "replayed certified proof changed")
    controlled = V / "certificates/model_schedule_work_conserving"
    target_only = {"WorkConservingCorrespondence", "WorkConservingExactTypeGuards",
                   "WorkConservingAssumptionAudit"}
    for name in MODULES:
        if name in target_only:
            original = controlled / f"{name}.v"
        elif name in ("PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence"):
            original = V / "certificates/common" / f"{name}.v"
        else:
            original = cert / f"{name}.v"
        staged = cert / f"{name}.v"
        vo = cert / f"{name}.vo"
        text = staged.read_text()
        if name == "PropSPropFoundation":
            need(text.count("Axiom interpret_strict :") == 1,
                 "approved Prop/SProp boundary changed")
            text = text.replace("Axiom interpret_strict :", "Definition audited_boundary :")
        need(sha(original) == sha(staged) and sha(vo)
             and vo.stat().st_mtime_ns > staged.stat().st_mtime_ns
             and not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", text),
             f"Rocq proof/source stale or forbidden: {name}")
    assumption_log = cert / "WorkConservingAssumptionAudit.log"
    summary = read(cert / "assumption_summary.json")
    need(sha(assumption_log) and summary["audit_policy"] == "fail_closed"
         and set(summary["certificates"]) == set(NAMES),
         "assumption output missing/truncated")
    for name, item in summary["certificates"].items():
        need(item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
             and item["semantic_premises"] == []
             and item["statement_only_dependencies"] == []
             and item["unexpected"] == []
             and item["prop_sprop_foundation"] == ["PropSPropFoundation.interpret_strict"]
             and not item["source_theorem_dependency"]
             and not item["target_theorem_dependency"],
             f"semantic audit failed: {name}")
    need(not output("git", "-C", str(ROOT), "status", "--porcelain", "--",
                    "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = V / "imported/translation_order/work_conserving"
    need(not destination.exists(), "already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".work-conserving.", dir=destination.parent))
    evidence = {"export": export, "export_metadata": WORK / "export_metadata.json",
                "imported_v": wrapper, "imported_vo": imported_vo,
                "source_type_audit": source_audit, "lean_audit": lean_audit,
                "export_log": export_log, "assumption_log": assumption_log,
                "assumption_summary": cert / "assumption_summary.json",
                "ready_instantiation": cert / "work_conserving_ready_instantiation.json",
                "arrival_instantiation": cert / "work_conserving_arrival_instantiation.json"}
    for path in evidence.values():
        shutil.copy2(path, stage / path.name)
    (stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(cert / f"{name}{suffix}", stage / "certificates" / f"{name}{suffix}")
    need(sha(stage / export.name) == sha(export)
         and sha(stage / imported_vo.name) == sha(imported_vo),
         "staged artifact corrupt")
    stage.rename(destination)
    artifacts = {"official_source": official, "source_copy": copied,
                 "source_vo": source_vo, "production_source": production,
                 "production_olean": olean, "export_config": config,
                 "assumption_config": controlled / "work_conserving_assumption_config.json",
                 "dependency_manifest": PIPE / "behavior_all_module_manifest.json",
                 "replay_script": replay}
    artifacts.update({key: destination / path.name for key, path in evidence.items()})
    for name in MODULES:
        artifacts[f"{name}_v"] = (controlled / f"{name}.v" if name in target_only else
                                   V / "certificates/common" / f"{name}.v" if name in
                                   ("PropSPropFoundation", "LogicalRelation",
                                    "SubadditivityNatCorrespondence") else
                                   destination / "certificates" / f"{name}.v")
        artifacts[f"{name}_vo"] = destination / "certificates" / f"{name}.vo"
    manifest = {
        "slice": "MODEL_SCHEDULE_WORK_CONSERVING", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": sha(official),
        "source_compatibility": "byte-identical official source; no patch",
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": f"Prosa.Model.Schedule.WorkConserving.{name}",
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": name + "_correspondence",
            "semantic_status": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
            "semantic_premises": [], "statement_only_dependencies": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        } for name, row in zip(NAMES, rows)],
        "artifact_hashes": {key + "_sha256": sha(path) for key, path in artifacts.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT)) for key, path in artifacts.items()
                           if path.is_relative_to(PROJECT)},
        "tooling_manifest_sha256": sha(V / "tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path = PIPE / "model_schedule_work_conserving_module_manifest.json"
    status_path = PIPE / "model_schedule_work_conserving_module_status.json"
    need(not manifest_path.exists() and not status_path.exists(), "machine state already published")
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {"public_declarations": 2, "translated": 2,
                              "proof_clean": 2, "certified": 0,
                              "certified_with_prop_sprop_foundation": 2,
                              "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**baseline["coverage"], "accepted_files": 57,
                     "accepted_declarations": 395},
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "accepted_files": 57,
                      "accepted_declarations": 395}, sort_keys=True))


if __name__ == "__main__":
    main()
