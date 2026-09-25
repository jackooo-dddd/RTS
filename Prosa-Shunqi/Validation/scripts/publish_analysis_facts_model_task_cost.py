#!/usr/bin/env python3
"""Fail-closed whole-file publication for v0.6 analysis/facts/model/task_cost.v."""

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
WORK = VALIDATION / ".work/experiments/analysis_facts_model_task_cost"
SOURCE = "analysis/facts/model/task_cost.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE_SHA = "35c06c53780a3df4b82074f21238cc36bb694367e8df3b031d764b3d2a3a3686"
LEAN_SHA = "8eaaa74f0c8e24ebe230750d98c6d392efbeaf5b6836f48cf122ae8c61f8a6d2"
OLEAN_SHA = "baf806b878dbe24f6292c12036705f3f75427e5fa2756830e3cf4123be78ef38"
EXPORT_SHA = "5c57025cd0f20448c882b795e242043d6cc5133f958b57541c80b4adafbc2333"
NAMES = ("job_cost_positive_implies_task_cost_positive", "sum_job_costs_bounded")
MODULES = (
    "TaskCostBaseAdapter", "TaskCostClasses", "TaskCostOperations",
    "TaskCostListOperations", "TaskCostLogicalOperations",
    "TaskCostPositiveCorrespondence", "TaskCostSumCorrespondence",
    "TaskCostExactTypeGuards", "TaskCostAssumptionAudit",
)
DEPS = {
    "behavior/all.v": ("behavior_all", "Prosa/Behavior/All.olean"),
    "model/job/properties.v": ("model_job_properties", "Prosa/Model/Job/Properties.olean"),
    "model/task/concept.v": ("model_task_concept", "Prosa/Model/Task/Concept.olean"),
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("TASK_COST_PUBLICATION_REJECTED: " + message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    require(path.is_file(), f"missing {path}")
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
    require(bool(candidates), "no cumulative PASS status")
    latest = max(candidates)
    require(sum(row[:2] == latest[:2] for row in candidates) == 1,
            "ambiguous latest cumulative status")
    require(latest[0] >= 64 and latest[1] >= 457,
            "Rank 68 accepted baseline missing")
    return latest[2], read(latest[2])


def main() -> None:
    previous_path, previous = latest_status()
    official_root = VALIDATION / ".work/prosa-v06-414e667"
    official = official_root / SOURCE
    require(output("git", "-C", str(official_root), "rev-parse", "HEAD") == PIN
            and not output("git", "-C", str(official_root), "status", "--porcelain",
                           "--untracked-files=all"), "pinned official source changed")
    require(sha(official) == SOURCE_SHA
            and sha(WORK / "source" / SOURCE) == SOURCE_SHA,
            "official source or compiled source copy changed")
    with (VALIDATION / "planning/v06_dependency/file_inventory.csv").open() as stream:
        source_row = next(row for row in csv.DictReader(stream)
                          if row["file"] == SOURCE)
    require(source_row["sha256"] == SOURCE_SHA
            and source_row["layer"] == "11", "source inventory changed")
    graph = read(VALIDATION / "planning/v06_dependency/file_dag.json")
    actual_deps = {edge["dependency_file"] for edge in graph["edges"]
                   if edge["dependent_file"] == SOURCE}
    require(actual_deps == set(DEPS), "authoritative file DAG changed")
    stage_root = WORK / "olean"
    for source_file, (stem, olean_path) in DEPS.items():
        manifest = read(PIPE / f"{stem}_module_manifest.json")
        status = read(PIPE / f"{stem}_module_status.json")
        production = PROJECT / Path(olean_path).with_suffix(".lean")
        require(manifest["acceptance"] == "ACCEPTED_V06_FILE"
                and status["status"] == "PASS"
                and manifest["source_file"] == source_file
                and sha(production) == manifest["production_source_sha256"]
                and sha(stage_root / olean_path) == manifest["production_olean_sha256"],
                f"accepted dependency mismatch: {source_file}")

    with (VALIDATION / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream)
                if row["source_file"] == SOURCE]
    require([row["declaration_name"] for row in rows] == list(NAMES)
            and all(row["kind"] == "Lemma" and
                    row["final_type_or_type_fingerprint"].startswith("rocq-check-sha256:")
                    for row in rows), "source declaration inventory changed")
    source_vo = WORK / "source/analysis/facts/model/task_cost.vo"
    require(sha(source_vo) and source_vo.stat().st_mtime_ns >
            (WORK / "source" / SOURCE).stat().st_mtime_ns,
            "source was not freshly compiled")
    source_guard = VALIDATION / "fixtures/translation_order/TaskCostSourceTypeAudit.v"
    source_guard_vo = source_guard.with_suffix(".vo")
    require(sha(source_guard) and sha(source_guard_vo)
            and source_guard_vo.stat().st_mtime_ns > source_vo.stat().st_mtime_ns,
            "official source elaborated-type guard missing")

    require("Lean (version 4.33.1" in output("lean", "--version")
            and output("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                       "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in output("opam", "exec", "--switch=rocq93rc1", "--",
                                "rocq", "--version"), "toolchain changed")
    tooling = read(VALIDATION / "tooling/tooling_manifest.json")
    require(sha(VALIDATION / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "tooling/foundation changed")

    production = PROJECT / "Prosa/Analysis/Facts/Model/TaskCost.lean"
    olean = stage_root / "Prosa/Analysis/Facts/Model/TaskCost.olean"
    lean_guard = VALIDATION / "fixtures/translation_order/TaskCostLeanTypeAudit.lean"
    lean_guard_olean = stage_root / "Validation/fixtures/translation_order/TaskCostLeanTypeAudit.olean"
    require(sha(production) == LEAN_SHA and sha(olean) == OLEAN_SHA
            and sha(lean_guard) and sha(lean_guard_olean)
            and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
            and lean_guard_olean.stat().st_mtime_ns > lean_guard.stat().st_mtime_ns
            and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text()),
            "fresh compiled Lean proof/statement freeze failed")
    lean_audit = (WORK / "lean_axiom_audit.log")
    require(sha(lean_audit), "Lean axiom audit log missing")
    lean_audit_text = lean_audit.read_text()
    for name in NAMES:
        require(f"TaskCost.{name}' depends on axioms: [propext]" in lean_audit_text,
                f"Lean #print axioms missing/unexpected: {name}")
    require("sorryAx" not in lean_audit_text and "error:" not in lean_audit_text.lower(),
            "Lean proof/axiom audit failed")

    export_config = VALIDATION / "tooling/analysis_facts_model_task_cost_export_config.json"
    config = read(export_config)
    expected_names = ["Prosa.Analysis.Facts.Model.TaskCost." + name for name in NAMES]
    require(config["targets"] == expected_names
            and config["body_theorems"] == expected_names
            and config["statement_only"] == [], "export policy changed")
    exported = WORK / "TaskCostFull.out"
    imported_v = WORK / "imported/ImportedTaskCost.v"
    imported_vo = WORK / "imported/ImportedTaskCost.vo"
    require(sha(exported) == EXPORT_SHA
            and sha(WORK / "imported/TaskCostFull.out") == EXPORT_SHA
            and sha(imported_v) and sha(imported_vo)
            and imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns
            and "Lean Import \"TaskCostFull.out\"" in imported_v.read_text()
            and "Error:" not in (WORK / "import.log").read_text(),
            "fresh actual compiled artifact export/import missing")

    controlled = VALIDATION / "certificates/analysis_facts_model_task_cost"
    cert_dir = WORK / "certificates"
    for name in MODULES:
        formal = controlled / f"{name}.v"
        copied = cert_dir / f"{name}.v"
        compiled = cert_dir / f"{name}.vo"
        require(sha(formal) == sha(copied) and sha(compiled)
                and compiled.stat().st_mtime_ns > copied.stat().st_mtime_ns
                and compiled.stat().st_mtime_ns > imported_vo.stat().st_mtime_ns
                and "Error:" not in (WORK / f"{name}.log").read_text()
                and not re.search(r"\b(Axiom|Admitted|admit|sorry)\b", formal.read_text()),
                f"actual-artifact Rocq certificate not clean: {name}")
    summary = read(WORK / "assumption_audit.json")
    require(summary.get("audit_policy") == "fail_closed"
            and set(summary.get("certificates", {})) == set(NAMES)
            and "AUDIT_END sum_job_costs_bounded" in
            (WORK / "TaskCostAssumptionAudit.log").read_text(),
            "assumption audit missing/truncated")
    for name in NAMES:
        item = summary["certificates"][name]
        require(item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and item["prop_sprop_foundation"] ==
                ["PropSPropFoundation.interpret_strict"]
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"],
                f"semantic/assumption gate failed: {name}")
    # Semantic correspondence must be compositional, not inferred from two
    # independently proved theorem truths. These named operation relations are
    # the actual proof dependencies of the two target certificates.
    positive_proof = (controlled / "TaskCostPositiveCorrespondence.v").read_text()
    sum_proof = (controlled / "TaskCostSumCorrespondence.v").read_text()
    require(all(token in positive_proof for token in
                ("tc_job_of_task_related", "tc_job_cost_positive_related",
                 "tc_valid_job_cost_related", "sub_nat_lt_correspondence"))
            and all(token in sum_proof for token in
                    ("tc_membership_correspondence", "tc_big_seq_sum_related",
                     "tc_length_related", "sub_nat_le_correspondence")),
            "structural semantic dependency DAG not present")
    require(not output("git", "-C", str(ROOT), "status", "--porcelain", "--",
                       "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = VALIDATION / "imported/translation_order/analysis_facts_model_task_cost"
    manifest_path = PIPE / "analysis_facts_model_task_cost_module_manifest.json"
    status_path = PIPE / "analysis_facts_model_task_cost_module_status.json"
    require(not destination.exists() and not manifest_path.exists()
            and not status_path.exists(), "TaskCost already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    staged = Path(tempfile.mkdtemp(prefix=".task-cost-", dir=destination.parent))
    evidence = {
        "source_vo": source_vo, "production_olean": olean,
        "lean_type_guard_olean": lean_guard_olean,
        "export": exported, "imported_v": imported_v,
        "imported_vo": imported_vo, "assumption_summary": WORK / "assumption_audit.json",
        "assumption_log": WORK / "TaskCostAssumptionAudit.log",
        "lean_axiom_audit_log": lean_audit,
    }
    for key, path in list(evidence.items()):
        target = staged / (key + path.suffix)
        shutil.copy2(path, target)
        require(sha(target) == sha(path), f"publication copy corrupted: {key}")
        evidence[key] = target
    (staged / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            source = cert_dir / (name + suffix)
            target = staged / "certificates" / source.name
            shutil.copy2(source, target)
            require(sha(target) == sha(source), f"certificate copy corrupted: {name}")
            evidence[name + suffix] = target
    staged.rename(destination)
    evidence = {key: destination / path.relative_to(staged)
                for key, path in evidence.items()}
    declarations = [{
        "source_declaration": row["qualified_name"],
        "lean_declaration": "Prosa.Analysis.Facts.Model.TaskCost." + row["declaration_name"],
        "kind": row["kind"],
        "source_command_sha256": row["source_command_sha256"],
        "source_elaborated_type_fingerprint": row["final_type_or_type_fingerprint"],
        "semantic_certificate": summary["certificates"][row["declaration_name"]]["certificate"],
        "semantic_status": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
        "semantic_premises": [], "statement_only_dependencies": [],
        "source_theorem_dependency": False, "target_theorem_dependency": False,
        "unexpected_assumptions": [],
        "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
        "acceptance": "ACCEPTED_V06_TRANSLATION",
    } for row in rows]
    manifest = {
        "slice": "ANALYSIS_FACTS_MODEL_TASK_COST", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": SOURCE_SHA,
        "direct_file_dependencies": sorted(DEPS),
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "validation_mode": "FILE_VALIDATE_WITH_VERIFIED_ACCEPTED_PRODUCERS",
        "target_build": "FRESH", "export": "FRESH", "rocq_import": "FRESH",
        "acceptance": "ACCEPTED_V06_FILE", "declarations": declarations,
        "artifact_hashes": {key + "_sha256": sha(path)
                            for key, path in evidence.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT))
                           for key, path in evidence.items()},
        "export_config_sha256": sha(export_config),
        "tooling_manifest_sha256": sha(VALIDATION / "tooling/tooling_manifest.json"),
        "previous_status_file": previous_path.name,
        "previous_status_sha256": sha(previous_path),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = {**previous["coverage"],
                "accepted_files": previous["coverage"]["accepted_files"] + 1,
                "accepted_declarations": previous["coverage"]["accepted_declarations"] + 2}
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 2, "translated": 2, "proof_clean": 2,
            "certified": 0, "certified_with_prop_sprop_foundation": 2,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": coverage, "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "coverage": coverage}, sort_keys=True))


if __name__ == "__main__":
    main()
