#!/usr/bin/env python3
"""Fail-closed publication of the actual Rank 65 TaskSchedule artifact."""

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
W = V / ".work/experiments/analysis_definitions_task_schedule"
SOURCE = "analysis/definitions/task_schedule.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
NAMES = (
    "scheduled_jobs_of_task_at", "task_scheduled_at", "task_service_at",
    "task_service_during", "task_service", "served_jobs_of_task_at",
    "task_served_at",
)
MODULES = (
    "PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence",
    "ArrivalSequenceBaseAdapter", "ArrivalSequenceOperations",
    "ServiceBaseAdapter", "ServiceNatBoolOperations",
    "ServiceIntervalOperations", "ServiceScheduleOperations",
    "TaskScheduleCorrespondence", "TaskScheduleExactTypeGuards",
)


def require(ok: bool, why: str) -> None:
    if not ok:
        raise SystemExit("TASK_SCHEDULE_PUBLICATION_REJECTED: " + why)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def output(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def latest_status() -> tuple[Path, dict]:
    candidates = []
    for path in PIPE.glob("*_module_status.json"):
        item = read(path)
        if item.get("status") == "PASS":
            coverage = item.get("coverage", {})
            candidates.append((coverage.get("accepted_files", -1),
                               coverage.get("accepted_declarations", -1), path))
    require(bool(candidates), "no formal cumulative status")
    last = max(candidates)
    require(sum(x[:2] == last[:2] for x in candidates) == 1,
            "ambiguous cumulative status")
    require(last[0] >= 61 and last[1] >= 441,
            "Rank 66 accepted baseline missing")
    return last[2], read(last[2])


def accepted_producer_corpus() -> list[str]:
    corpus = []
    for path in PIPE.glob("*manifest.json"):
        item = read(path)
        status_path = path.with_name(path.name.replace("manifest.json", "status.json"))
        if not status_path.is_file():
            continue
        status = read(status_path)
        if item.get("acceptance") == "ACCEPTED_V06_FILE" and status.get("status") == "PASS":
            corpus.append(path.read_text())
        elif path.name in (
            "foundation_slice_1_manifest.json",
            "foundation_slice_2_closure_manifest.json",
            "utility_foundation_expansion_manifest.json",
        ) and any(status.get(key) == "PASS" for key in (
            "FOUNDATION_SLICE_1_STATUS", "FOUNDATION_SLICE_2_CLOSURE_STATUS",
            "UTILITY_FOUNDATION_EXPANSION_STATUS",
        )):
            corpus.append(path.read_text())
    require(len(corpus) >= 50, "accepted producer evidence incomplete")
    return corpus


def main() -> None:
    previous_path, previous = latest_status()
    official_root = V / ".work/prosa-v06-414e667"
    official = official_root / SOURCE
    source = W / "source" / SOURCE
    source_vo = source.with_suffix(".vo")
    require(output("git", "-C", str(official_root), "rev-parse", "HEAD") == PIN
            and output("git", "-C", str(official_root), "rev-parse", "HEAD^{tree}") == TREE
            and not output("git", "-C", str(official_root), "status", "--porcelain",
                           "--untracked-files=all"),
            "pinned official source not exact/clean")
    with (V / "planning/v06_dependency/file_inventory.csv").open() as stream:
        file_row = next(r for r in csv.DictReader(stream) if r["file"] == SOURCE)
    require(file_row["sha256"] == sha(official) == sha(source)
            and file_row["layer"] == "11"
            and source_vo.stat().st_mtime_ns > source.stat().st_mtime_ns,
            "official source or fresh Rocq build mismatch")
    graph = read(V / "planning/v06_dependency/file_dag.json")
    deps = {e["dependency_file"] for e in graph["edges"]
            if e["dependent_file"] == SOURCE}
    require(deps == {"analysis/definitions/service.v", "model/schedule/scheduled.v",
                     "model/task/concept.v"}, "file DAG changed")
    for stem in ("analysis_service", "model_schedule_scheduled",
                 "model_task_concept"):
        manifest = read(PIPE / f"{stem}_module_manifest.json")
        status = read(PIPE / f"{stem}_module_status.json")
        require(manifest.get("acceptance") == "ACCEPTED_V06_FILE"
                and status.get("status") == "PASS"
                and sha(PROJECT / manifest["production_file"])
                == manifest["production_source_sha256"],
                f"accepted dependency changed: {stem}")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    require([r["declaration_name"] for r in rows] == list(NAMES)
            and all(r["kind"] == "Definition" for r in rows),
            "public source inventory mismatch")
    types = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    require(all(r["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + types[r["qualified_name"]]["sha256"]
                for r in rows), "official elaborated type evidence changed")

    require("Lean (version 4.33.1" in output("lake", "env", "lean", "--version")
            and output("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                       "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in output("opam", "exec", "--switch=rocq93rc1",
                                "--", "rocq", "--version"),
            "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    require(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Analysis/Definitions/TaskSchedule.lean"
    olean_root = W / "olean"
    olean = olean_root / "Prosa/Analysis/Definitions/TaskSchedule.olean"
    iface = V / "fixtures/translation_order/TaskScheduleComputationInterface.lean"
    iface_olean = olean_root / "Validation/fixtures/translation_order/TaskScheduleComputationInterface.olean"
    for src, artifact in ((production, olean), (iface, iface_olean)):
        require(sha(src) and sha(artifact)
                and artifact.stat().st_mtime_ns > src.stat().st_mtime_ns
                and not re.search(r"\b(sorry|axiom|unsafe)\b", src.read_text()),
                f"Lean source/build invalid: {src}")
    # Bigcat and ArrivalSequence interfaces lacked a paired source hash in
    # early manifests, so this run rebuilt both against accepted producers.
    rebuilt_interfaces = ("BigcatComputationInterface",
                          "ArrivalSequenceComputationInterface")
    for name in rebuilt_interfaces:
        src = V / f"fixtures/translation_order/{name}.lean"
        artifact = olean_root / f"Validation/fixtures/translation_order/{name}.olean"
        require(sha(src) and sha(artifact)
                and artifact.stat().st_mtime_ns > src.stat().st_mtime_ns,
                f"validation-only computation interface not rebuilt: {name}")
    corpus = accepted_producer_corpus()
    dependency_oleans = [p for p in olean_root.rglob("*.olean")
                         if p not in {olean, iface_olean}
                         and p.name not in {name + ".olean" for name in rebuilt_interfaces}]
    for artifact in dependency_oleans:
        src = PROJECT / artifact.relative_to(olean_root).with_suffix(".lean")
        require(any(sha(artifact) in text and sha(src) in text for text in corpus),
                f"unverified dependency olean/source pair: {artifact}")
    lean_audit = V / "fixtures/translation_order/TaskScheduleLeanAxiomAudit.lean"
    lean_log = W / "lean_axiom_audit.log"
    lean_summary = read(W / "task_schedule_lean_axiom_audit.json")
    require(sha(lean_audit) and "error:" not in lean_log.read_text().lower()
            and "sorryAx" not in lean_log.read_text()
            and lean_summary.get("audit_policy") == "fail_closed"
            and len(lean_summary["declarations"]) == 11
            and all(x["status"] == "PASS" and not x["unexpected_axioms"]
                    for x in lean_summary["declarations"].values())
            and not lean_summary["missing"] and not lean_summary["extra"],
            "Lean proof-clean audit failed")

    export_config = V / "tooling/analysis_definitions_task_schedule_export_config.json"
    config = read(export_config)
    exported = W / "imported/TaskSchedule.out"
    wrapper = W / "imported/ImportedTaskSchedule.v"
    imported = W / "imported/ImportedTaskSchedule.vo"
    export_log = (W / "export.log").read_text()
    require(config["module"] ==
            "Validation.fixtures.translation_order.TaskScheduleComputationInterface"
            and config["targets"][:7] == [
                "Prosa.Analysis.Definitions.TaskSchedule." + name for name in NAMES]
            and config["statement_only"] == []
            and len(config["normalization"]["body_projections"]) == 4
            and export_log.count("kernel_rfl_guard=true") == 4
            and sha(exported) and sha(wrapper) and sha(imported)
            and imported.stat().st_mtime_ns > exported.stat().st_mtime_ns
            and wrapper.read_text() ==
            'From LeanImport Require Import Lean.\nLean Import "TaskSchedule.out".\n'
            and "Error:" not in (W / "import_lean.log").read_text(),
            "fresh guarded actual-artifact export/import invalid")
    controlled = V / "certificates/analysis_definitions_task_schedule"
    compiled = W / "certificates"
    for name in MODULES:
        proof, vo = compiled / f"{name}.v", compiled / f"{name}.vo"
        text = proof.read_text()
        if name == "PropSPropFoundation":
            require(sha(proof) == sha(V / "certificates/common/PropSPropFoundation.v")
                    and len(re.findall(r"\bAxiom\b", text)) == 1
                    and "Axiom interpret_strict :" in text
                    and not re.search(r"\b(Admitted|admit|sorry)\b", text),
                    "approved Prop/SProp foundation changed")
        else:
            require(not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", text),
                    f"forbidden proof gap: {name}")
        require(sha(proof) and sha(vo)
                and vo.stat().st_mtime_ns > proof.stat().st_mtime_ns
                and "Error:" not in (compiled / f"{name}.log").read_text(),
                f"Rocq certificate invalid: {name}")
    for name in ("TaskScheduleCorrespondence", "TaskScheduleExactTypeGuards"):
        require(sha(compiled / f"{name}.v") == sha(controlled / f"{name}.v"),
                f"controlled certificate changed: {name}")
    assumption_config = controlled / "task_schedule_assumption_config.json"
    summary = read(W / "task_schedule_assumption_summary.json")
    require(read(assumption_config)["imported_artifact_sha256"] == sha(imported)
            and summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(NAMES)
            and "AUDIT_END" in (compiled / "TaskScheduleCorrespondence.log").read_text(),
            "assumption log missing/truncated or bound to stale import")
    for name in NAMES:
        item = summary["certificates"][name]
        require(item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and item["prop_sprop_foundation"] == ["interpret_strict"]
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"],
                f"semantic assumption audit failed: {name}")
    inventory = read(W / "task_schedule_operation_inventory_audit.json")
    require(inventory.get("status") == "PASS"
            and inventory.get("missing_operations") == []
            and len(inventory["declarations"]) == 7
            and len(inventory["certified_bridges"]) == 18,
            "operation dependency inventory not closed")
    require(not output("git", "-C", str(ROOT), "status", "--porcelain", "--",
                       "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = V / "imported/translation_order/analysis_definitions_task_schedule"
    manifest_path = PIPE / "analysis_definitions_task_schedule_module_manifest.json"
    status_path = PIPE / "analysis_definitions_task_schedule_module_status.json"
    require(not destination.exists() and not manifest_path.exists()
            and not status_path.exists(), "already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".task-schedule-", dir=destination.parent))
    artifacts = {
        "official_source": official, "source_vo": source_vo,
        "production_source": production, "production_olean": olean,
        "computation_interface": iface, "computation_interface_olean": iface_olean,
        "lean_axiom_audit_source": lean_audit,
        "lean_axiom_audit_summary": W / "task_schedule_lean_axiom_audit.json",
        "export_config": export_config, "export": exported,
        "imported_v": wrapper, "imported_vo": imported,
        "assumption_config": assumption_config,
        "assumption_summary": W / "task_schedule_assumption_summary.json",
        "operation_inventory": W / "task_schedule_operation_inventory_audit.json",
    }
    for key, path in (("export", exported), ("imported_v", wrapper),
                      ("imported_vo", imported), ("source_vo", source_vo),
                      ("assumption_summary", W / "task_schedule_assumption_summary.json"),
                      ("operation_inventory", W / "task_schedule_operation_inventory_audit.json"),
                      ("lean_axiom_audit_summary", W / "task_schedule_lean_axiom_audit.json")):
        shutil.copy2(path, stage / path.name)
        artifacts[key] = stage / path.name
    (stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(compiled / f"{name}{suffix}",
                         stage / "certificates" / f"{name}{suffix}")
            artifacts[f"{name}{suffix}"] = stage / "certificates" / f"{name}{suffix}"
    require(sha(stage / imported.name) == sha(imported)
            and sha(stage / exported.name) == sha(exported),
            "publication stage corrupted")
    stage.rename(destination)
    artifacts = {key: destination / path.relative_to(stage)
                 if path.is_relative_to(stage) else path
                 for key, path in artifacts.items()}
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        item = summary["certificates"][name]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Analysis.Definitions.TaskSchedule." + name,
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
    manifest = {
        "slice": "ANALYSIS_DEFINITIONS_TASK_SCHEDULE",
        "source_commit": PIN, "source_file": SOURCE,
        "source_file_sha256": sha(official),
        "source_acquisition": {"mode": "FRESH", "proof_only_compat_patch": None},
        "direct_file_dependencies": sorted(deps),
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "validation_mode": "FILE_VALIDATE_WITH_VERIFIED_ACCEPTED_PRODUCERS",
        "target_build": "FRESH", "export": "FRESH", "rocq_import": "FRESH",
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": declarations,
        "artifact_hashes": {key + "_sha256": sha(path)
                            for key, path in artifacts.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT))
                           for key, path in artifacts.items()
                           if path.is_relative_to(PROJECT)},
        "tooling_manifest_sha256": sha(V / "tooling/tooling_manifest.json"),
        "previous_status_file": previous_path.name,
        "previous_status_sha256": sha(previous_path),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = {**previous["coverage"],
                "accepted_files": previous["coverage"]["accepted_files"] + 1,
                "accepted_declarations": previous["coverage"]["accepted_declarations"] + 7}
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 7, "translated": 7, "proof_clean": 7,
            "certified": 0, "certified_with_prop_sprop_foundation": 7,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": coverage, "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": status["status"], "coverage": coverage}, sort_keys=True))


if __name__ == "__main__":
    main()
