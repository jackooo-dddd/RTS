#!/usr/bin/env python3
"""Fail-closed publication of pinned v0.6 model/schedule/scheduled.v."""

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
WORK = V / ".work/experiments/model_schedule_scheduled"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE = "model/schedule/scheduled.v"
NAMES = ("scheduled_jobs_at", "scheduled_job_at", "is_idle")
DEPS = ("arrivals_up_to_dependency", "filter_dependency", "scheduled_in_dependency",
        "scheduled_at_dependency", "head_dependency", "empty_dependency")
MODULES = ("PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence",
           "ReadyArrivalBaseAdapter", "ReadyArrivalOperations",
           "ReadyArrivalCorrespondence", "ScheduledStateBaseAdapter",
           "ScheduledStateOperations", "ScheduledCorrespondence",
           "ScheduledExactTypeGuards", "ScheduledAssumptionAudit")


def need(ok: bool, why: str) -> None:
    if not ok:
        raise SystemExit(f"SCHEDULED_PUBLICATION_REJECTED: {why}")


def digest(path: Path) -> str:
    need(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def shell(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read(PIPE / "model_schedule_scheduled_selection.json")
    baseline = read(PIPE / "model_schedule_nonpreemptive_module_status.json")
    need(selection["source_commit"] == PIN and selection["source_file"] == SOURCE
         and selection["rank"] == 59 and selection["layer"] == 10
         and selection["file_dag_ready"]
         and selection["direct_internal_dependencies"] == ["behavior/all.v", "util/epsilon.v"]
         and selection["targets_in_source_order"] == list(NAMES)
         and selection["public_declaration_count"] == 3,
         "selection/DAG mismatch")
    need(baseline["status"] == "PASS"
         and baseline["coverage"]["accepted_files"] == 55
         and baseline["coverage"]["accepted_declarations"] == 390,
         "previous accepted state changed")
    pinned = V / ".work/prosa-v06-414e667"
    official = pinned / SOURCE
    copied = WORK / "source" / SOURCE
    source_vo = copied.with_suffix(".vo")
    need(shell("git", "-C", str(pinned), "rev-parse", "HEAD") == PIN
         and shell("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}")
         == "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
         and not shell("git", "-C", str(pinned), "status", "--porcelain",
                       "--untracked-files=all")
         and digest(official) == digest(copied) == selection["source_sha256"]
         and digest(source_vo)
         and source_vo.stat().st_mtime_ns > copied.stat().st_mtime_ns,
         "official pinned source/fresh compile invalid")
    need(digest(pinned / "util/epsilon.v") == digest(WORK / "source/util/epsilon.v")
         and digest(WORK / "source/util/epsilon.vo"),
         "Require Export epsilon source/interface absent")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    need([r["declaration_name"] for r in rows] == list(NAMES),
         "public source inventory changed")
    types = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        need(row["final_type_or_type_fingerprint"] ==
             "rocq-check-sha256:" + types[row["qualified_name"]]["sha256"],
             f"elaborated source type changed: {row['declaration_name']}")
    source_audit = WORK / "source_type_audit.log"
    need("Error:" not in source_audit.read_text()
         and all("@" + x in source_audit.read_text() for x in NAMES),
         "official Check/Print audit incomplete")
    for name, rel in (("behavior_all", "Prosa/Behavior/All.olean"),
                      ("epsilon", "Prosa/Util/Epsilon.olean")):
        manifest = read(PIPE / f"{name}_module_manifest.json")
        status = read(PIPE / f"{name}_module_status.json")
        need(manifest["acceptance"] == "ACCEPTED_V06_FILE"
             and status["status"] == "PASS"
             and digest(PROJECT / manifest["production_file"])
             == manifest["production_source_sha256"]
             and digest(WORK / "olean" / rel)
             == manifest["production_olean_sha256"],
             f"accepted dependency drift: {name}")
    need("Lean (version 4.33.1" in shell("lake", "env", "lean", "--version")
         and shell("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                   "rev-parse", "HEAD")
         == "0df444a360eaa60ab8c11dca51a86af692955474"
         and "9.3" in shell("opam", "exec", "--switch=rocq93rc1", "--",
                            "rocq", "--version"), "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    need(digest(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
         == tooling["lean4export"]["expected_binary_sha256"]
         and digest(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
         == tooling["rocq_lean_import"]["expected_plugin_sha256"]
         and digest(V / ".work/tooling/rocq-lean-import/src/Lean.vo")
         == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
         "tooling/foundation changed")
    production = PROJECT / "Prosa/Model/Schedule/Scheduled.lean"
    olean = WORK / "olean/Prosa/Model/Schedule/Scheduled.olean"
    lean_log = WORK / "lean_type_audit.log"
    need(digest(production) and digest(olean)
         and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
         and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text())
         and "error:" not in lean_log.read_text()
         and "sorryAx" not in lean_log.read_text()
         and "1 : ℕ" in lean_log.read_text()
         and all("'Prosa.Model.Schedule.Scheduled." + name +
                 "' depends on axioms: [propext, Classical.choice, Quot.sound]"
                 in lean_log.read_text() for name in NAMES),
         "Lean compiled interface/proof-clean check failed")
    for name in ("Bigcat", "Schedule", "Scheduled"):
        v = V / f"fixtures/translation_order/{name}ComputationInterface.lean"
        vo = WORK / f"olean/Validation/fixtures/translation_order/{name}ComputationInterface.olean"
        need(digest(v) and digest(vo) and vo.stat().st_mtime_ns > v.stat().st_mtime_ns,
             f"computation guard fixture stale: {name}")
    config = V / "tooling/model_schedule_scheduled_export_config.json"
    export = WORK / "imported/ScheduledFull.out"
    meta = read(WORK / "export_metadata.json")
    cfg = read(config)
    need(cfg["module"] == "Validation.fixtures.translation_order.ScheduledComputationInterface"
         and cfg["targets"][:3] == [f"Prosa.Model.Schedule.Scheduled.{x}" for x in NAMES]
         and cfg["statement_only"] == []
         and not any(cfg["normalization"].values())
         and meta["config_sha256"] == digest(config)
         and meta["output_sha256"] == digest(export)
         and meta["statement_only_count"] == 0,
         "actual full-body export/config changed")
    imported = WORK / "imported"
    wrapper = imported / "ImportedScheduledFull.v"
    imported_vo = imported / "ImportedScheduledFull.vo"
    need(wrapper.read_text() ==
         'From LeanImport Require Import Lean.\nLean Import "ScheduledFull.out".\n'
         and digest(imported_vo)
         and imported_vo.stat().st_mtime_ns > export.stat().st_mtime_ns
         and imported_vo.stat().st_mtime_ns > wrapper.stat().st_mtime_ns,
         "actual Lean artifact import absent/stale")
    generated = read(WORK / "certificates/scheduled_arrival_instantiation.json")
    need(generated["imported_artifact_sha256"] == digest(imported_vo),
         "generated arrival adapter not bound to this import")
    for item in generated["generated"].values():
        need(digest(PROJECT / item["source"]) == item["source_sha256"]
             and digest(PROJECT / item["output"]) == item["output_sha256"],
             "replayed accepted arrival proof drift")
    cert = V / "certificates/model_schedule_scheduled"
    compiled = WORK / "certificates"
    for name in MODULES:
        original = (cert if name not in ("PropSPropFoundation", "LogicalRelation",
                                         "SubadditivityNatCorrespondence")
                    else V / "certificates/common") / f"{name}.v"
        staged = compiled / f"{name}.v"
        vo = compiled / f"{name}.vo"
        text = staged.read_text()
        if name == "PropSPropFoundation":
            need(text.count("Axiom interpret_strict :") == 1,
                 "approved Prop/SProp foundation changed")
            text = text.replace("Axiom interpret_strict :", "Definition audited_boundary :")
        need(digest(original) == digest(staged) and digest(vo)
             and vo.stat().st_mtime_ns > staged.stat().st_mtime_ns
             and not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", text),
             f"kernel certificate/source changed: {name}")
    log = compiled / "ScheduledAssumptionAudit.log"
    summary = read(WORK / "assumption_summary.json")
    need(digest(log) and summary["audit_policy"] == "fail_closed"
         and set(summary["certificates"]) == set(NAMES) | set(DEPS),
         "Print Assumptions missing/truncated")
    for name, item in summary["certificates"].items():
        need(item["status"] in ("CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")
             and item["semantic_premises"] == []
             and item["statement_only_dependencies"] == []
             and item["unexpected"] == []
             and not item["source_theorem_dependency"]
             and not item["target_theorem_dependency"]
             and (item["prop_sprop_foundation"] == ["PropSPropFoundation.interpret_strict"]
                  if item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                  else item["prop_sprop_foundation"] == []),
             f"assumption audit failed: {name}")
    need(not shell("git", "-C", str(ROOT), "status", "--porcelain", "--",
                   "Prosa-fei"), "historical workspace modified")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)
    destination = V / "imported/translation_order/scheduled"
    need(not destination.exists(), "already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".scheduled.", dir=destination.parent))
    evidence = {"export": export, "export_metadata": WORK / "export_metadata.json",
                "imported_v": wrapper, "imported_vo": imported_vo,
                "source_type_audit": source_audit, "lean_type_audit": lean_log,
                "assumption_log": log, "assumption_summary": WORK / "assumption_summary.json",
                "arrival_instantiation": WORK / "certificates/scheduled_arrival_instantiation.json"}
    for path in evidence.values():
        shutil.copy2(path, stage / path.name)
    (stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(compiled / f"{name}{suffix}", stage / "certificates" / f"{name}{suffix}")
    need(digest(stage / export.name) == digest(export)
         and digest(stage / imported_vo.name) == digest(imported_vo),
         "staged artifact corrupted")
    stage.rename(destination)
    artifacts = {"official_source": official, "source_copy": copied,
                 "source_vo": source_vo, "production_source": production,
                 "production_olean": olean, "export_config": config,
                 "assumption_config": cert / "scheduled_assumption_config.json",
                 "behavior_all_manifest": PIPE / "behavior_all_module_manifest.json",
                 "epsilon_manifest": PIPE / "epsilon_module_manifest.json"}
    artifacts.update({key: destination / path.name for key, path in evidence.items()})
    for name in MODULES:
        artifacts[f"{name}_v"] = (cert if name not in (
            "PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence")
            else V / "certificates/common") / f"{name}.v"
        artifacts[f"{name}_vo"] = destination / "certificates" / f"{name}.vo"
    manifest = {
        "slice": "MODEL_SCHEDULE_SCHEDULED", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": digest(official),
        "source_compatibility": "byte-identical official source; no patch",
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": digest(production),
        "production_olean_sha256": digest(olean),
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": f"Prosa.Model.Schedule.Scheduled.{name}",
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": types[row["qualified_name"]]["sha256"],
            "semantic_certificate": name + "_correspondence",
            "semantic_status": summary["certificates"][name]["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation": summary["certificates"][name]["prop_sprop_foundation"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        } for name, row in zip(NAMES, rows)],
        "artifact_hashes": {key + "_sha256": digest(path) for key, path in artifacts.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT)) for key, path in artifacts.items()
                           if path.is_relative_to(PROJECT)},
        "tooling_manifest_sha256": digest(V / "tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path = PIPE / "model_schedule_scheduled_module_manifest.json"
    status_path = PIPE / "model_schedule_scheduled_module_status.json"
    need(not manifest_path.exists() and not status_path.exists(), "machine state already published")
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {"public_declarations": 3, "translated": 3,
                              "proof_clean": 3, "certified": 0,
                              "certified_with_prop_sprop_foundation": 3,
                              "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**baseline["coverage"], "accepted_files": 56,
                     "accepted_declarations": 393},
        "manifest_sha256": digest(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "accepted_files": 56,
                      "accepted_declarations": 393}, sort_keys=True))


if __name__ == "__main__":
    main()
