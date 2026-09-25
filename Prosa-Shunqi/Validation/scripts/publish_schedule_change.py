#!/usr/bin/env python3
"""Fail-closed, serial publication of pinned schedule_change.v."""

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
W = V / ".work/experiments/analysis_definitions_overheads_schedule_change"
PIPE = V / "planning/v06_pipeline"
SOURCE = "analysis/definitions/overheads/schedule_change.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
NAMES = (
    "schedule_change", "number_schedule_changes",
    "no_schedule_changes_during", "scheduled_job_invariant",
)
MODULES = (
    "ScheduleChangeBaseAdapter", "ScheduleChangeStateAdapter",
    "ScheduleChangeOptionOperations", "ScheduleChangeIntervalOperations",
    "ScheduleChangeListOperations", "ScheduleChangeCorrespondence",
    "ScheduleChangeExactTypeGuards", "ScheduleChangeAssumptionAudit",
)


def need(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit("SCHEDULE_CHANGE_PUBLICATION_REJECTED: " + message)


def sha(path: Path) -> str:
    need(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read(PIPE / "analysis_definitions_overheads_schedule_change_selection.json")
    previous_path = PIPE / "model_task_concept_module_status.json"
    previous = read(previous_path)
    need(selection["source_file"] == SOURCE and selection["source_commit"] == PIN
         and selection["rank"] == 64 and selection["layer"] == 11
         and selection["direct_internal_dependencies"] == ["model/processor/overheads.v"]
         and selection["file_dag_ready"]
         and selection["targets_in_source_order"] == list(NAMES)
         and previous["status"] == "PASS"
         and previous["coverage"]["accepted_files"] == 58
         and previous["coverage"]["accepted_declarations"] == 414,
         "selection/DAG/previous formal state changed")
    pinned = V / ".work/prosa-v06-414e667"
    official = pinned / SOURCE
    source_copy = W / "source" / SOURCE
    source_vo = source_copy.with_suffix(".vo")
    need(command("git", "-C", str(pinned), "rev-parse", "HEAD") == PIN
         and command("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}")
         == "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
         and not command("git", "-C", str(pinned), "status", "--porcelain",
                         "--untracked-files=all")
         and sha(official) == sha(source_copy) == selection["source_sha256"]
         and sha(source_vo) and source_vo.stat().st_mtime_ns > source_copy.stat().st_mtime_ns,
         "official source provenance/compile changed")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    need([r["declaration_name"] for r in rows] == list(NAMES),
         "source public inventory changed")
    types = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        need(row["final_type_or_type_fingerprint"] ==
             "rocq-check-sha256:" + types[row["qualified_name"]]["sha256"],
             f"official elaborated type changed: {row['declaration_name']}")
    source_audit = W / "source_type_audit.log"
    need("Error:" not in source_audit.read_text()
         and all("@" + n in source_audit.read_text() for n in NAMES),
         "official source Check/Print missing")

    dep = read(PIPE / "model_processor_overheads_module_manifest.json")
    dep_status = read(PIPE / "model_processor_overheads_module_status.json")
    need(dep["acceptance"] == "ACCEPTED_V06_FILE"
         and dep_status["status"] == "PASS"
         and sha(PROJECT / dep["artifact_paths"]["production_source"])
         == dep["artifact_hashes"]["production_source"]
         and sha(W / "olean/Prosa/Model/Processor/Overheads.olean")
         == dep["artifact_hashes"]["production_olean"]
         and sha(W / "source/model/processor/overheads.vo")
         == dep["artifact_hashes"]["source_vo"],
         "accepted Overheads dependency changed")
    need("Lean (version 4.33.1" in command("lake", "env", "lean", "--version")
         and command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                     "rev-parse", "HEAD")
         == "0df444a360eaa60ab8c11dca51a86af692955474"
         and "9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                              "rocq", "--version"),
         "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    need(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
         == tooling["lean4export"]["expected_binary_sha256"]
         and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
         == tooling["rocq_lean_import"]["expected_plugin_sha256"]
         and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo")
         == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
         "tooling/importer foundation changed")

    production = PROJECT / "Prosa/Analysis/Definitions/Overheads/ScheduleChange.lean"
    olean = W / "olean/Prosa/Analysis/Definitions/Overheads/ScheduleChange.olean"
    lean_audit = W / "lean_type_audit.log"
    audit_text = lean_audit.read_text()
    need(sha(production) and sha(olean)
         and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
         and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text())
         and "error:" not in audit_text and "sorryAx" not in audit_text
         and all("@" + n + " :" in audit_text for n in NAMES)
         and all(re.search(
             rf"'Prosa\.Analysis\.Definitions\.Overheads\.ScheduleChange\.{n}' "
             r"depends on axioms: \[propext,\s*Classical\.choice,\s*Quot\.sound\]",
             audit_text) for n in NAMES),
         "Lean build/type/proof-clean audit changed")
    interface = V / "fixtures/translation_order/ScheduleChangeComputationInterface.lean"
    interface_olean = W / (
        "olean/Validation/fixtures/translation_order/ScheduleChangeComputationInterface.olean")
    need(sha(interface_olean) and interface_olean.stat().st_mtime_ns > interface.stat().st_mtime_ns,
         "compiled computation equations stale")
    config_path = V / "tooling/analysis_definitions_overheads_schedule_change_export_config.json"
    config = read(config_path)
    export = W / "portable/imported/ScheduleChangeFull.out"
    meta = read(W / "export_metadata.json")
    need(config["module"] ==
         "Validation.fixtures.translation_order.ScheduleChangeComputationInterface"
         and config["targets"][:4] ==
         [f"Prosa.Analysis.Definitions.Overheads.ScheduleChange.{n}" for n in NAMES]
         and config["statement_only"] == []
         and not any(config["normalization"].values())
         and len(config["body_theorems"]) == 13
         and meta["config_sha256"] == sha(config_path)
         and meta["output_sha256"] == sha(export)
         and meta["statement_only_count"] == 0
         and meta["body_theorem_count"] == 13,
         "actual compiled export changed")
    imported = W / "portable/imported"
    wrapper = imported / "ImportedScheduleChange.v"
    imported_vo = imported / "ImportedScheduleChange.vo"
    need(wrapper.read_text() ==
         'From LeanImport Require Import Lean.\nLean Import "ScheduleChangeFull.out".\n'
         and sha(imported_vo)
         and imported_vo.stat().st_mtime_ns > export.stat().st_mtime_ns
         and imported_vo.stat().st_mtime_ns > wrapper.stat().st_mtime_ns,
         "fresh imported artifact missing/stale")

    controlled = V / "certificates/analysis_definitions_overheads_schedule_change"
    compiled = W / "portable/certificates"
    for name in MODULES:
        v, vo = compiled / f"{name}.v", compiled / f"{name}.vo"
        need(sha(v) == sha(controlled / f"{name}.v")
             and sha(vo) and vo.stat().st_mtime_ns > v.stat().st_mtime_ns
             and not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", v.read_text()),
             f"certificate missing/stale/forbidden: {name}")
    summary = read(W / "assumption_summary.json")
    assumption_config = controlled / "schedule_change_assumption_config.json"
    need(summary["audit_policy"] == "fail_closed"
         and set(summary["certificates"]) == set(read(assumption_config)["certificates"])
         and len(summary["certificates"]) == 9
         and "AUDIT_END scheduled_job_invariant" in
             (W / "ScheduleChangeAssumptionAudit.log").read_text(),
         "assumption audit missing/truncated")
    for name, item in summary["certificates"].items():
        need(item["status"] in {"CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
             and item["semantic_premises"] == []
             and item["statement_only_dependencies"] == []
             and item["unexpected"] == []
             and not item["source_theorem_dependency"]
             and not item["target_theorem_dependency"]
             and item["prop_sprop_foundation"] ==
             (["PropSPropFoundation.interpret_strict"]
              if item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" else []),
             f"semantic gate failed: {name}")
    for name in NAMES:
        need(summary["certificates"][name]["status"] ==
             "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
             f"target status changed: {name}")
    need(not command("git", "-C", str(ROOT), "status", "--porcelain", "--", "Prosa-fei"),
         "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    dest = V / "imported/translation_order/schedule_change"
    manifest_path = PIPE / "analysis_definitions_overheads_schedule_change_module_manifest.json"
    status_path = PIPE / "analysis_definitions_overheads_schedule_change_module_status.json"
    need(not dest.exists() and not manifest_path.exists() and not status_path.exists(),
         "already published")
    dest.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".schedule-change.", dir=dest.parent))
    for path in (export, W / "export_metadata.json", wrapper, imported_vo,
                 W / "assumption_summary.json", W / "source_type_audit.log",
                 lean_audit, W / "ScheduleChangeAssumptionAudit.log", W / "export.log"):
        shutil.copy2(path, stage / path.name)
    (stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(compiled / f"{name}{suffix}",
                         stage / "certificates" / f"{name}{suffix}")
    need(sha(stage / export.name) == sha(export)
         and sha(stage / imported_vo.name) == sha(imported_vo),
         "publication staging corruption")
    stage.rename(dest)
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        item = summary["certificates"][name]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration":
                f"Prosa.Analysis.Definitions.Overheads.ScheduleChange.{name}",
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": types[row["qualified_name"]]["sha256"],
            "semantic_certificate": item["certificate"],
            "semantic_status": item["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    artifacts = {
        "official_source": official, "source_copy": source_copy,
        "source_vo": source_vo, "production_source": production,
        "production_olean": olean, "computation_interface": interface,
        "computation_interface_olean": interface_olean,
        "export_config": config_path, "assumption_config": assumption_config,
        "export": dest / export.name, "export_metadata": dest / "export_metadata.json",
        "imported_v": dest / wrapper.name, "imported_vo": dest / imported_vo.name,
        "assumption_summary": dest / "assumption_summary.json",
        "source_type_audit": dest / "source_type_audit.log",
        "lean_type_audit": dest / "lean_type_audit.log",
    }
    for name in MODULES:
        artifacts[f"{name}_v"] = dest / "certificates" / f"{name}.v"
        artifacts[f"{name}_vo"] = dest / "certificates" / f"{name}.vo"
    manifest = {
        "slice": "ANALYSIS_DEFINITIONS_OVERHEADS_SCHEDULE_CHANGE",
        "source_commit": PIN, "source_file": SOURCE,
        "source_file_sha256": sha(official),
        "source_compatibility": "byte-identical official source; no target patch",
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": declarations,
        "artifact_hashes": {k + "_sha256": sha(p) for k, p in artifacts.items()},
        "artifact_paths": {k: str(p.relative_to(PROJECT)) for k, p in artifacts.items()
                           if p.is_relative_to(PROJECT)},
        "tooling_manifest_sha256": sha(V / "tooling/tooling_manifest.json"),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 4, "translated": 4, "proof_clean": 4,
            "certified": 0, "certified_with_prop_sprop_foundation": 4,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": {**previous["coverage"], "accepted_files": 59,
                     "accepted_declarations": 418},
        "previous_status": str(previous_path.relative_to(PROJECT)),
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "accepted_files": 59,
                      "accepted_declarations": 418}, sort_keys=True))


if __name__ == "__main__":
    main()
