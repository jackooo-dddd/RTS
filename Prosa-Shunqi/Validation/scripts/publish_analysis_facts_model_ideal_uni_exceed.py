#!/usr/bin/env python3
"""Fail-closed publication of the pinned ideal_uni_exceed facts file."""

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
W = V / ".work/experiments/analysis_facts_model_ideal_uni_exceed"
SOURCE = "analysis/facts/model/ideal_uni_exceed.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
NAMES = (
    "eps_is_unit_supply",
    "scheduled_at_procstate",
    "eps_is_uniproc",
    "eps_is_fully_consuming",
    "eps_is_unit_service",
    "is_exceedance_exec",
    "blackout_implies_exceedance_execution",
)
MODULES = (
    "IdealUniExceedFactsBaseAdapter",
    "IdealUniExceedFactsSourceOperations",
    "IdealUniExceedFactsStateCorrespondence",
    "IdealUniExceedFactsSourceComputation",
    "IdealUniExceedFactsOperations",
    "IdealUniExceedFactsCorrespondence",
    "IdealUniExceedFactsExactTypeGuards",
    "IdealUniExceedFactsModelCorrespondence",
    "IdealUniExceedFactsScheduledStatement",
    "IdealUniExceedFactsBlackoutStatement",
    "IdealUniExceedFactsAssumptionAudit",
)


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise SystemExit("IDEAL_UNI_EXCEED_FACTS_PUBLICATION_REJECTED: " + reason)


def digest(path: Path) -> str:
    need(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def output(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def latest_status() -> Path:
    candidates = []
    for path in PIPE.glob("*_module_status.json"):
        data = read(path)
        if data.get("status") == "PASS":
            coverage = data.get("coverage", {})
            candidates.append(
                (coverage.get("accepted_files", -1),
                 coverage.get("accepted_declarations", -1), path)
            )
    need(bool(candidates), "no accepted cumulative state")
    latest = max(candidates)
    need(sum((a, b) == latest[:2] for a, b, _ in candidates) == 1,
         "ambiguous latest cumulative state")
    need(latest[:2] == (59, 418), "cumulative state changed; rerun integration")
    need(latest[2].name ==
         "analysis_definitions_overheads_schedule_change_module_status.json",
         "unexpected previous status")
    return latest[2]


def main() -> None:
    previous_path = latest_status()
    previous = read(previous_path)
    pinned = V / ".work/prosa-v06-414e667"
    official = pinned / SOURCE
    source_copy = W / "source" / SOURCE
    source_vo = source_copy.with_suffix(".vo")
    source_patch = V / "patches/prosa-v06-rocq93-analysis-facts-model-ideal-uni-exceed.patch"
    need(output("git", "-C", str(pinned), "rev-parse", "HEAD") == PIN
         and output("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}") == TREE
         and not output("git", "-C", str(pinned), "status", "--porcelain",
                        "--untracked-files=all"),
         "authoritative source checkout changed")
    with (V / "planning/v06_dependency/file_inventory.csv").open() as stream:
        file_row = next(r for r in csv.DictReader(stream) if r["file"] == SOURCE)
    need(file_row["layer"] == "11" and file_row["direct_internal_import_count"] == "2"
         and file_row["sha256"] == digest(official), "file inventory/source mismatch")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    need([r["declaration_name"] for r in rows] == list(NAMES),
         "public declaration inventory mismatch")
    types = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        need(row["final_type_or_type_fingerprint"] ==
             "rocq-check-sha256:" + types[row["qualified_name"]]["sha256"],
             f"source elaborated type changed: {row['declaration_name']}")
    dag = read(V / "planning/v06_dependency/file_dag.json")
    deps = {e["dependency_file"] for e in dag["edges"]
            if e["dependent_file"] == SOURCE}
    need(deps == {"model/processor/ideal_uni_exceed.v",
                  "model/processor/platform_properties.v"},
         "authoritative file DAG changed")
    for stem in ("model_processor_ideal_uni_exceed",
                 "model_processor_platform_properties"):
        dep_manifest = read(PIPE / f"{stem}_module_manifest.json")
        dep_status = read(PIPE / f"{stem}_module_status.json")
        dep_file = (dep_manifest.get("production_file")
                    or dep_manifest.get("translation_file")
                    or dep_manifest.get("artifact_paths", {}).get("production_source"))
        dep_sha = (dep_manifest.get("production_source_sha256")
                   or dep_manifest.get("artifact_hashes", {}).get(
                       "production_source_sha256")
                   or dep_manifest.get("artifact_hashes", {}).get(
                       "production_source"))
        need(dep_manifest["acceptance"] == "ACCEPTED_V06_FILE"
             and dep_status["status"] == "PASS"
             and dep_file is not None and dep_sha is not None
             and digest(PROJECT / dep_file) == dep_sha,
             f"accepted dependency changed: {stem}")
    with tempfile.TemporaryDirectory(prefix="ideal-uni-exceed-source-") as folder:
        expected = Path(folder) / SOURCE
        expected.parent.mkdir(parents=True)
        shutil.copy2(official, expected)
        subprocess.run(["patch", "-s", "-p1", "-d", folder, "-i", str(source_patch)],
                       check=True)
        need(digest(expected) == digest(source_copy),
             "source compatibility patch differs from compiled source")
    need(digest(source_vo)
         and source_vo.stat().st_mtime_ns > source_copy.stat().st_mtime_ns
         and "Error:" not in (W / "merged_source_type_audit.log").read_text()
         and all("@" + name in
                 (W / "merged_source_type_audit.log").read_text() for name in NAMES),
         "source compile/elaborated type audit missing")

    need("Lean (version 4.33.1" in output("lake", "env", "lean", "--version")
         and output("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD")
         == "0df444a360eaa60ab8c11dca51a86af692955474"
         and "9.3" in output("opam", "exec", "--switch=rocq93rc1",
                             "--", "rocq", "--version"),
         "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    need(digest(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
         == tooling["lean4export"]["expected_binary_sha256"]
         and digest(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
         == tooling["rocq_lean_import"]["expected_plugin_sha256"]
         and digest(V / ".work/tooling/rocq-lean-import/src/Lean.vo")
         == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
         "export/import tooling changed")
    production = PROJECT / "Prosa/Analysis/Facts/Model/IdealUniExceed.lean"
    olean = W / "olean/Prosa/Analysis/Facts/Model/IdealUniExceed.olean"
    interface = V / "fixtures/translation_order/IdealUniExceedFactsComputationInterface.lean"
    interface_olean = W / "olean/Validation/fixtures/translation_order/IdealUniExceedFactsComputationInterface.olean"
    lean_log = W / "merged_lean_type_audit.log"
    need(digest(production) and digest(olean) and digest(interface)
         and digest(interface_olean)
         and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
         and interface_olean.stat().st_mtime_ns > interface.stat().st_mtime_ns
         and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text())
         and "error:" not in lean_log.read_text().lower()
         and "sorryAx" not in lean_log.read_text()
         and all("@Prosa.Analysis.Facts.Model.IdealUniExceed." + name + " :"
                 in lean_log.read_text() for name in NAMES)
         and all(re.search(
             rf"'Prosa\.Analysis\.Facts\.Model\.IdealUniExceed\.{name}' "
             r"depends on axioms: \[propext,\s*Classical\.choice,\s*Quot\.sound\]",
             lean_log.read_text()) for name in NAMES),
         "Lean fresh build/type/proof-clean audit failed")
    config_path = V / "tooling/analysis_facts_model_ideal_uni_exceed_export_config.json"
    config = read(config_path)
    exported = W / "merged_reexport.out"
    imported = W / "portable/imported"
    wrapper = imported / "ImportedIdealUniExceedFacts.v"
    imported_vo = imported / "ImportedIdealUniExceedFacts.vo"
    need(config["module"] ==
         "Validation.fixtures.translation_order.IdealUniExceedFactsComputationInterface"
         and config["targets"][:7] ==
         [f"Prosa.Analysis.Facts.Model.IdealUniExceed.{name}" for name in NAMES]
         and len(config["statement_only"]) == 6
         and not any(config["normalization"].values())
         and digest(exported) == digest(imported / "IdealUniExceedFacts.out")
         and wrapper.read_text() ==
         'From LeanImport Require Import Lean.\nLean Import "IdealUniExceedFacts.out".\n'
         and digest(imported_vo)
         and imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns
         and "Error:" not in (W / "merged_import.log").read_text(),
         "actual compiled export/import evidence missing")
    controlled = V / "certificates/analysis_facts_model_ideal_uni_exceed"
    compiled = W / "portable/certificates"
    for name in MODULES:
        v, vo = compiled / f"{name}.v", compiled / f"{name}.vo"
        need(digest(v) == digest(controlled / f"{name}.v")
             and digest(vo) and vo.stat().st_mtime_ns > v.stat().st_mtime_ns
             and not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", v.read_text())
             and "Error:" not in (W / f"merged_{name}.log").read_text(),
             f"certificate not fresh/controlled/proof-clean: {name}")
    summary = read(W / "merged_assumption_summary.json")
    assumption_config = controlled / "ideal_uni_exceed_facts_assumption_config.json"
    need(summary["audit_policy"] == "fail_closed"
         and set(summary["certificates"]) == set(read(assumption_config)["certificates"])
         and "AUDIT_END blackout_implies_exceedance_execution"
         in (W / "merged_IdealUniExceedFactsAssumptionAudit.log").read_text(),
         "assumption audit missing/truncated")
    for name in NAMES:
        item = summary["certificates"][name]
        expected = ("CERTIFIED" if name == "is_exceedance_exec"
                    else "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")
        need(item["status"] == expected
             and item["semantic_premises"] == []
             and item["statement_only_dependencies"] == []
             and item["unexpected"] == []
             and not item["source_theorem_dependency"]
             and not item["target_theorem_dependency"]
             and item["prop_sprop_foundation"] ==
             ([] if expected == "CERTIFIED"
              else ["PropSPropFoundation.interpret_strict"]),
             f"semantic assumption gate failed: {name}")
    need(not output("git", "-C", str(ROOT), "status", "--porcelain", "--",
                    "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = V / "imported/translation_order/ideal_uni_exceed_facts"
    manifest_path = PIPE / "analysis_facts_model_ideal_uni_exceed_module_manifest.json"
    status_path = PIPE / "analysis_facts_model_ideal_uni_exceed_module_status.json"
    need(not destination.exists() and not manifest_path.exists() and not status_path.exists(),
         "already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".ideal-uni-exceed-facts-",
                                  dir=destination.parent))
    for source, name in (
        (exported, "IdealUniExceedFacts.out"),
        (wrapper, wrapper.name),
        (imported_vo, imported_vo.name),
        (W / "merged_assumption_summary.json", "assumption_summary.json"),
        (W / "merged_source_type_audit.log", "source_type_audit.log"),
        (lean_log, "lean_type_audit.log"),
        (W / "merged_IdealUniExceedFactsAssumptionAudit.log",
         "assumption_audit.log"),
        (W / "merged_reexport.log", "export.log"),
        (W / "merged_import.log", "import.log"),
    ):
        shutil.copy2(source, stage / name)
    (stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(compiled / f"{name}{suffix}",
                         stage / "certificates" / f"{name}{suffix}")
    need(digest(stage / "IdealUniExceedFacts.out") == digest(exported)
         and digest(stage / imported_vo.name) == digest(imported_vo),
         "publication stage corrupted")
    stage.rename(destination)

    artifacts = {
        "official_source": official,
        "source_copy": source_copy,
        "source_vo": source_vo,
        "source_compatibility_patch": source_patch,
        "production_source": production,
        "production_olean": olean,
        "computation_interface": interface,
        "computation_interface_olean": interface_olean,
        "export_config": config_path,
        "assumption_config": assumption_config,
        "export": destination / "IdealUniExceedFacts.out",
        "imported_v": destination / wrapper.name,
        "imported_vo": destination / imported_vo.name,
        "assumption_summary": destination / "assumption_summary.json",
        "source_type_audit": destination / "source_type_audit.log",
        "lean_type_audit": destination / "lean_type_audit.log",
        "assumption_audit": destination / "assumption_audit.log",
    }
    for name in MODULES:
        artifacts[f"{name}_v"] = destination / "certificates" / f"{name}.v"
        artifacts[f"{name}_vo"] = destination / "certificates" / f"{name}.vo"
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        item = summary["certificates"][name]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": f"Prosa.Analysis.Facts.Model.IdealUniExceed.{name}",
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": types[row["qualified_name"]]["sha256"],
            "semantic_certificate": item["certificate"],
            "semantic_status": item["status"],
            "semantic_premises": [],
            "statement_only_dependencies": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation": item["prop_sprop_foundation"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": "ANALYSIS_FACTS_MODEL_IDEAL_UNI_EXCEED",
        "source_commit": PIN,
        "source_file": SOURCE,
        "source_file_sha256": digest(official),
        "source_compatibility": "validation-only Rocq 9.3 local proof lemma; target statements unchanged",
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": digest(production),
        "production_olean_sha256": digest(olean),
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": declarations,
        "artifact_hashes": {key + "_sha256": digest(path)
                            for key, path in artifacts.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT))
                           for key, path in artifacts.items()
                           if path.is_relative_to(PROJECT)},
        "tooling_manifest_sha256": digest(V / "tooling/tooling_manifest.json"),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = {**previous["coverage"],
                "accepted_files": previous["coverage"]["accepted_files"] + 1,
                "accepted_declarations":
                    previous["coverage"]["accepted_declarations"] + len(NAMES)}
    status = {
        "slice": manifest["slice"],
        "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": len(NAMES),
            "translated": len(NAMES),
            "proof_clean": len(NAMES),
            "certified": 1,
            "certified_with_prop_sprop_foundation": 6,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": coverage,
        "previous_status": str(previous_path.relative_to(PROJECT)),
        "manifest_sha256": digest(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "coverage": coverage}, sort_keys=True))


if __name__ == "__main__":
    main()
