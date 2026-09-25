#!/usr/bin/env python3
"""Fail-closed, whole-file publication for pinned v0.6 model/schedule/edf.v."""

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
WORK = VALIDATION / ".work/experiments/model_schedule_edf"
PORTABLE = WORK / "portable"
PIPE = VALIDATION / "planning/v06_pipeline"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE = "model/schedule/edf.v"
NAMES = ("EDF_at", "EDF_schedule")
CERTIFICATES = ("EDF_at_correspondence", "EDF_schedule_correspondence")
MODULES = (
    "EdfBaseAdapter", "EdfOperations", "EdfCorrespondence",
    "EdfExactTypeGuards", "EdfAssumptionAudit",
)


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise SystemExit(f"EDF_PUBLICATION_REJECTED: {reason}")


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def output(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read_json(PIPE / "model_schedule_edf_selection.json")
    baseline = read_json(PIPE / "model_processor_varspeed_module_status.json")
    require(selection["source_commit"] == PIN and selection["source_file"] == SOURCE
            and selection["rank"] == 57 and selection["layer"] == 10
            and selection["file_dag_ready"]
            and selection["direct_internal_dependencies"] == ["behavior/all.v"]
            and selection["targets_in_source_order"] == list(NAMES)
            and selection["public_declaration_count"] == 2,
            "selection/DAG/inventory mismatch")
    require(baseline["status"] == "PASS"
            and baseline["coverage"]["accepted_files"] == 53
            and baseline["coverage"]["accepted_declarations"] == 387,
            "previous accepted state changed")

    pinned = VALIDATION / ".work/prosa-v06-414e667"
    official = pinned / SOURCE
    source_copy = WORK / "source" / SOURCE
    require(output("git", "-C", str(pinned), "rev-parse", "HEAD") == PIN
            and output("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}")
            == "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
            and not output("git", "-C", str(pinned), "status", "--porcelain",
                           "--untracked-files=all")
            and sha(official) == selection["source_sha256"] == sha(source_copy),
            "official source not pinned/byte-identical")
    source_vo = source_copy.with_suffix(".vo")
    require(sha(source_vo) and source_vo.stat().st_mtime_ns > source_copy.stat().st_mtime_ns,
            "official Rocq source compile missing/stale")
    source_types = (WORK / "source_type_audit.log").read_text()
    require("Error:" not in source_types
            and all(f"@{name}" in source_types for name in NAMES),
            "official elaborated type audit incomplete")
    with (VALIDATION / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    require([r["declaration_name"] for r in rows] == list(NAMES),
            "public declaration inventory changed")
    type_evidence = read_json(VALIDATION / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
                f"source type fingerprint changed: {row['declaration_name']}")

    dep = read_json(PIPE / "behavior_all_module_manifest.json")
    dep_status = read_json(PIPE / "behavior_all_module_status.json")
    require(dep["acceptance"] == "ACCEPTED_V06_FILE"
            and dep_status["status"] == "PASS"
            and sha(PROJECT / dep["production_file"]) == dep["production_source_sha256"]
            and sha(WORK / "olean/Prosa/Behavior/All.olean")
            == dep["production_olean_sha256"],
            "accepted Behavior.All dependency changed")
    require("Lean (version 4.33.1" in output("lake", "env", "lean", "--version")
            and output("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                       "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in output("opam", "exec", "--switch=rocq93rc1",
                                "--", "rocq", "--version"),
            "toolchain changed")
    tooling = read_json(VALIDATION / "tooling/tooling_manifest.json")
    require(sha(VALIDATION / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Model/Schedule/Edf.lean"
    olean = WORK / "olean/Prosa/Model/Schedule/Edf.olean"
    require(sha(production) and sha(olean)
            and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
            and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text()),
            "production Lean body/proof-clean freeze failed")
    lean_audit = (WORK / "lean_audit.log").read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit
            and all(f"'Prosa.Model.Schedule.Edf.{name}' depends on axioms: "
                    "[propext, Classical.choice, Quot.sound]" in lean_audit
                    for name in NAMES),
            "Lean elaborated type/body or axiom audit changed")
    fixture = VALIDATION / "fixtures/translation_order/EdfExportInterface.lean"
    fixture_olean = WORK / "olean/Validation/fixtures/translation_order/EdfExportInterface.olean"
    schedule_guard = VALIDATION / "fixtures/translation_order/ScheduleComputationInterface.lean"
    schedule_guard_olean = WORK / "olean/Validation/fixtures/translation_order/ScheduleComputationInterface.olean"
    require(sha(fixture_olean) and sha(schedule_guard_olean)
            and fixture_olean.stat().st_mtime_ns > fixture.stat().st_mtime_ns
            and schedule_guard_olean.stat().st_mtime_ns > schedule_guard.stat().st_mtime_ns,
            "export/computation guard fixture compile stale")

    config_path = VALIDATION / "tooling/model_schedule_edf_export_config.json"
    config = read_json(config_path)
    exported = WORK / "EdfFull.out"
    meta = read_json(WORK / "export_metadata.json")
    require(config["module"] == "Validation.fixtures.translation_order.EdfExportInterface"
            and config["targets"] == [f"Prosa.Model.Schedule.Edf.{x}" for x in NAMES] + [
                "Prosa.Behavior.Service.scheduled_at",
                "Prosa.Behavior.Schedule.ProcessorState.scheduled_in",
                "Prosa.Behavior.Job.JobArrival.job_arrival",
                "Prosa.Behavior.Job.JobDeadline.job_deadline",
                "Prosa.Validation.ScheduleInterface.production_scheduled_in_eq_true_iff"]
            and config["body_theorems"] == [
                "Prosa.Validation.ScheduleInterface.production_scheduled_in_eq_true_iff"]
            and config["statement_only"] == []
            and not any(config["normalization"].values())
            and meta["config_sha256"] == sha(config_path)
            and meta["output_sha256"] == sha(exported),
            "actual compiled target export/config differs")
    imported = PORTABLE / "imported"
    wrapper = imported / "ImportedEdfFull.v"
    imported_vo = imported / "ImportedEdfFull.vo"
    require(sha(imported / exported.name) == sha(exported)
            and wrapper.read_text() ==
            'From LeanImport Require Import Lean.\nLean Import "EdfFull.out".\n'
            and sha(imported_vo)
            and imported_vo.stat().st_mtime_ns > wrapper.stat().st_mtime_ns
            and imported_vo.stat().st_mtime_ns > (imported / exported.name).stat().st_mtime_ns,
            "actual exported Lean artifact not freshly imported")
    accepted_subadditivity = VALIDATION / "imported/foundation_slice_2_closure/Subadditivity.out"
    require(sha(imported / "Subadditivity.out") == sha(accepted_subadditivity)
            and sha(imported / "ImportedSubadditivity.vo"),
            "Nat foundation reimport not tied to accepted artifact")

    controlled = VALIDATION / "certificates/model_schedule_edf"
    compiled = PORTABLE / "certificates"
    for name in MODULES:
        original = controlled / f"{name}.v"
        copied = compiled / f"{name}.v"
        vo = compiled / f"{name}.vo"
        require(sha(original) == sha(copied) and sha(vo)
                and vo.stat().st_mtime_ns > copied.stat().st_mtime_ns
                and not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", copied.read_text()),
                f"certificate source/compiled artifact invalid: {name}")
    assumption_log = WORK / "EdfAssumptionAudit.log"
    summary = read_json(WORK / "assumption_summary.json")
    require(sha(assumption_log) and summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) ==
            {"scheduled_in_dependency", "scheduled_at_dependency", *NAMES},
            "assumption output missing/truncated")
    for target, item in summary["certificates"].items():
        require(item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and item["prop_sprop_foundation"] ==
                ["PropSPropFoundation.interpret_strict"]
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"],
                f"semantic assumption gate failed: {target}")
    require(not output("git", "-C", str(ROOT), "status", "--porcelain", "--",
                       "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = VALIDATION / "imported/translation_order/edf"
    require(not destination.exists(), "publication destination already exists")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".edf.", dir=destination.parent))
    for path in (exported, WORK / "export_metadata.json", wrapper, imported_vo,
                 assumption_log, WORK / "assumption_summary.json",
                 WORK / "source_type_audit.log", WORK / "lean_audit.log"):
        shutil.copy2(path, stage / path.name)
    (stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(compiled / f"{name}{suffix}",
                         stage / "certificates" / f"{name}{suffix}")
    require(sha(stage / exported.name) == sha(exported)
            and sha(stage / imported_vo.name) == sha(imported_vo),
            "staged artifact corrupt")
    stage.rename(destination)

    artifacts = {
        "official_source": official,
        "source_copy": source_copy,
        "source_vo": source_vo,
        "production_source": production,
        "production_olean": olean,
        "export_fixture": fixture,
        "export_fixture_olean": fixture_olean,
        "schedule_guard_fixture": schedule_guard,
        "schedule_guard_olean": schedule_guard_olean,
        "export_config": config_path,
        "export_metadata": destination / "export_metadata.json",
        "export": destination / exported.name,
        "imported_v": destination / wrapper.name,
        "imported_vo": destination / imported_vo.name,
        "assumption_log": destination / assumption_log.name,
        "assumption_summary": destination / "assumption_summary.json",
        "source_type_audit": destination / "source_type_audit.log",
        "lean_audit": destination / "lean_audit.log",
        "assumption_config": controlled / "edf_assumption_config.json",
        "behavior_all_manifest": PIPE / "behavior_all_module_manifest.json",
    }
    for name in MODULES:
        artifacts[f"{name}_v"] = controlled / f"{name}.v"
        artifacts[f"{name}_vo"] = destination / "certificates" / f"{name}.vo"
    manifest = {
        "slice": "MODEL_SCHEDULE_EDF",
        "source_commit": PIN,
        "source_file": SOURCE,
        "source_file_sha256": sha(official),
        "source_compatibility": "byte-identical official source; no patch",
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [
            {
                "source_declaration": row["qualified_name"],
                "lean_declaration": f"Prosa.Model.Schedule.Edf.{name}",
                "kind": "Definition",
                "source_command_sha256": row["source_command_sha256"],
                "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
                "semantic_certificate": cert,
                "semantic_status": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
                "semantic_premises": [],
                "statement_only_dependencies": [],
                "source_theorem_dependency": False,
                "target_theorem_dependency": False,
                "unexpected_assumptions": [],
                "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
                "acceptance": "ACCEPTED_V06_TRANSLATION",
            }
            for name, row, cert in zip(NAMES, rows, CERTIFICATES)
        ],
        "artifact_hashes": {key + "_sha256": sha(path) for key, path in artifacts.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT))
                           for key, path in artifacts.items() if path.is_relative_to(PROJECT)},
        "tooling_manifest_sha256": sha(VALIDATION / "tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path = PIPE / "model_schedule_edf_module_manifest.json"
    status_path = PIPE / "model_schedule_edf_module_status.json"
    require(not manifest_path.exists() and not status_path.exists(),
            "formal machine publication already exists")
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {"public_declarations": 2, "translated": 2,
                              "proof_clean": 2, "certified": 0,
                              "certified_with_prop_sprop_foundation": 2,
                              "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**baseline["coverage"], "accepted_files": 54,
                     "accepted_declarations": 389},
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "accepted_files": 54,
                      "accepted_declarations": 389}, sort_keys=True))


if __name__ == "__main__":
    main()
