#!/usr/bin/env python3
"""Fail-closed publication of pinned analysis/facts/behavior/supply.v."""

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
W = V / ".work/experiments/analysis_facts_behavior_supply"
PRIVATE = (Path("/private/tmp/prosa-v06-workers.PDi19y")
           / "analysis-facts-behavior-supply/Prosa-Shunqi"
           / "Validation/.work/experiments/analysis_facts_behavior_supply")
SOURCE = "analysis/facts/behavior/supply.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
NAMES = (
    "service_at_le_supply_at", "pos_service_impl_pos_supply",
    "blackout_or_supply", "supply_at_complement", "is_blackout_complement",
    "supply_at_le_1", "unit_supply_proc_service_case", "supply_during_bound",
    "blackout_during_bound", "supply_during_last_plus_before",
    "blackout_during_last_plus_before", "supply_during_complement",
    "blackout_during_complement", "blackout_during_cat",
    "blackout_during_unit_growth", "progress_inside_supplies",
)
MODULES = (
    "PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence",
    "FsScheduleBaseAdapter", "FsScheduleFiniteOperations",
    "FsScheduleCorrespondence", "FsProcessorStateCorrespondence",
    "SupplyBaseAdapter", "SupplyNatBoolOperations", "SupplyIntervalOperations",
    "FactsSupplyPlatformPropertiesCorrespondence",
    "FactsSupplyOperationCorrespondence",
    "FactsSupplyStatementCorrespondence", "FactsSupplyExactTypeGuards",
    "FactsSupplyAssumptionAudit",
)
CONTROLLED = (
    "FactsSupplyPlatformPropertiesCorrespondence",
    "FactsSupplyOperationCorrespondence",
    "FactsSupplyStatementCorrespondence", "FactsSupplyExactTypeGuards",
    "FactsSupplyAssumptionAudit",
)


def need(ok: bool, reason: str) -> None:
    if not ok:
        raise SystemExit("FACTS_BEHAVIOR_SUPPLY_PUBLICATION_REJECTED: " + reason)


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
            candidates.append((
                coverage.get("accepted_files", -1),
                coverage.get("accepted_declarations", -1), path
            ))
    need(bool(candidates), "no formal cumulative status")
    latest = max(candidates)
    need(sum(item[:2] == latest[:2] for item in candidates) == 1,
         "ambiguous previous cumulative status")
    need(latest[0] >= 60 and latest[1] >= 425,
         "Rank67 publication missing or stale")
    return latest[2]


def accepted_dependency(stem: str) -> dict:
    manifest = read(PIPE / f"{stem}_module_manifest.json")
    status = read(PIPE / f"{stem}_module_status.json")
    path = (manifest.get("production_file") or manifest.get("translation_file")
            or manifest.get("artifact_paths", {}).get("production_source"))
    expected = (manifest.get("production_source_sha256")
                or manifest.get("artifact_hashes", {}).get("production_source_sha256")
                or manifest.get("artifact_hashes", {}).get("production_source"))
    need(manifest["acceptance"] == "ACCEPTED_V06_FILE"
         and status["status"] == "PASS"
         and path is not None and expected is not None
         and digest(PROJECT / path) == expected,
         f"accepted dependency changed: {stem}")
    return manifest


def main() -> None:
    previous_path = latest_status()
    previous = read(previous_path)
    pinned = V / ".work/prosa-v06-414e667"
    official = pinned / SOURCE
    source_copy = W / "source_compat" / SOURCE
    source_vo = source_copy.with_suffix(".vo")
    private_source = PRIVATE / "source_compat" / SOURCE
    private_vo = private_source.with_suffix(".vo")
    patch = V / "patches/analysis_facts_behavior_supply_rocq93_source_compat.patch"
    need(output("git", "-C", str(pinned), "rev-parse", "HEAD") == PIN
         and output("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}") == TREE
         and not output("git", "-C", str(pinned), "status", "--porcelain",
                        "--untracked-files=all"),
         "authoritative source checkout changed")
    with (V / "planning/v06_dependency/file_inventory.csv").open() as stream:
        file_row = next(r for r in csv.DictReader(stream) if r["file"] == SOURCE)
    need(file_row["layer"] == "11"
         and file_row["sha256"] == digest(official)
         and file_row["direct_internal_import_count"] == "2",
         "authoritative file inventory mismatch")
    dag = read(V / "planning/v06_dependency/file_dag.json")
    dependencies = {e["dependency_file"] for e in dag["edges"]
                    if e["dependent_file"] == SOURCE}
    need(dependencies == {"model/processor/platform_properties.v", "util/all.v"},
         "authoritative file DAG changed")
    accepted_dependency("model_processor_platform_properties")
    accepted_dependency("behavior_all")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    need([r["declaration_name"] for r in rows] == list(NAMES),
         "public declaration inventory changed")
    types = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        need(row["final_type_or_type_fingerprint"] ==
             "rocq-check-sha256:" + types[row["qualified_name"]]["sha256"],
             f"official elaborated type changed: {row['declaration_name']}")
    need(digest(patch) ==
         "5f6ba56fb6e54d6ad2b67388be13a9b4e6c870f0bd741b4539569bf1ff83945c",
         "source compatibility patch changed")
    with tempfile.TemporaryDirectory(prefix="facts-behavior-supply-source-") as folder:
        expected = Path(folder) / SOURCE
        expected.parent.mkdir(parents=True)
        shutil.copy2(official, expected)
        subprocess.run(["patch", "-s", "-p1", "-d", folder, "-i", str(patch)],
                       check=True)
        need(digest(expected) == digest(source_copy) == digest(private_source),
             "compiled source copy is not exact pinned source plus audited patch")
    # The worker's already kernel-checked source artifact is a declared cache
    # boundary, not a claimed clean source rebuild in the main worktree.
    need(digest(source_vo) == digest(private_vo)
         and private_vo.stat().st_mtime_ns > private_source.stat().st_mtime_ns
         and "Error:" not in (W / "merged_source_type_audit.log").read_text()
         and all("@" + name in
                 (W / "merged_source_type_audit.log").read_text() for name in NAMES),
         "verified worker source artifact/type audit missing")

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
         "tooling/importer foundation changed")
    production = PROJECT / "Prosa/Analysis/Facts/Behavior/Supply.lean"
    olean = W / "olean/Prosa/Analysis/Facts/Behavior/Supply.olean"
    interface = V / "fixtures/translation_order/FactsBehaviorSupplyComputationInterface.lean"
    interface_olean = W / "olean/Validation/fixtures/translation_order/FactsBehaviorSupplyComputationInterface.olean"
    lean_audit = V / "fixtures/translation_order/FactsBehaviorSupplyLeanTypeAudit.lean"
    lean_log = W / "merged_lean_type_audit.log"
    need(digest(production) and digest(olean) and digest(interface)
         and digest(interface_olean) and digest(lean_audit)
         and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
         and interface_olean.stat().st_mtime_ns > interface.stat().st_mtime_ns
         and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text())
         and "error:" not in lean_log.read_text().lower()
         and "sorryAx" not in lean_log.read_text()
         and all("@" + name + " :" in lean_log.read_text() for name in NAMES)
         and all(re.search(
             rf"'Prosa\.Analysis\.Facts\.Behavior\.Supply\.{name}' "
             r"depends on axioms: \[propext,\s*Classical\.choice,\s*Quot\.sound\]",
             lean_log.read_text()) for name in NAMES),
         "Lean build/type/proof-clean audit missing")
    # Every transitive producer .olean must be tied to a formally accepted
    # producer and to that producer's current Lean source. Early accepted
    # utility files use slice-level manifests rather than module manifests.
    accepted_producers = {}
    for path in PIPE.glob("*manifest.json"):
        data = read(path)
        if data.get("acceptance") == "ACCEPTED_V06_FILE":
            hashes = data.get("artifact_hashes", {})
            accepted_producers[
                data.get("production_olean_sha256")
                or hashes.get("production_olean")
            ] = (
                data.get("production_source_sha256")
                or hashes.get("production_source"), path.name)
    slice1 = read(PIPE / "foundation_slice_1_manifest.json")
    slice1_status = read(PIPE / "foundation_slice_1_status.json")
    need(slice1_status.get("FOUNDATION_SLICE_1_STATUS") == "PASS"
         and slice1_status.get("coverage", {}).get("accepted_files") == 1
         and slice1.get("production_file") == "Prosa/Behavior/Time.lean",
         "foundational time producer not formally accepted")
    accepted_producers[slice1["artifacts"]["fresh_olean_sha256"]] = (
        slice1["artifacts"]["lean_source_sha256"],
        "foundation_slice_1_manifest.json")
    for stem in ("foundation_slice_2_closure", "utility_foundation_expansion"):
        manifest = read(PIPE / f"{stem}_manifest.json")
        status = read(PIPE / f"{stem}_status.json")
        need(status.get("coverage", {}).get("accepted_files", 0) >= 7,
             f"legacy accepted slice status missing: {stem}")
        for source_file, item in status["per_file"].items():
            if item.get("status") != "ACCEPTED_V06_FILE":
                continue
            if stem == "foundation_slice_2_closure":
                row = manifest["files"].get(source_file)
                if row:
                    accepted_producers[row["fresh_olean_sha256"]] = (
                        row["lean_source_sha256"], stem)
            else:
                for row in manifest["clusters"]:
                    if row.get("source_file") == source_file:
                        accepted_producers[row["fresh_olean_sha256"]] = (
                            row["lean_source_sha256"], stem)
    dependency_oleans = [p for p in (W / "olean/Prosa").rglob("*.olean")
                         if p != olean]
    need(len(dependency_oleans) >= 29
         and all(
             digest(path) in accepted_producers
             and accepted_producers[digest(path)][0]
             == digest(PROJECT / path.relative_to(W / "olean").with_suffix(".lean"))
             for path in dependency_oleans),
         "transitive accepted producer .olean hash not published")
    config_path = V / "tooling/analysis_facts_behavior_supply_export_config.json"
    config = read(config_path)
    exported = W / "merged_reexport.out"
    imported = W / "merged_imported"
    wrapper = imported / "ImportedFactsBehaviorSupply.v"
    imported_vo = imported / "ImportedFactsBehaviorSupply.vo"
    need(config["module"] ==
         "Validation.fixtures.translation_order.FactsBehaviorSupplyComputationInterface"
         and config["targets"][:16] ==
         [f"Prosa.Analysis.Facts.Behavior.Supply.{name}" for name in NAMES]
         and len(config["statement_only"]) == 16
         and len(config["normalization"]["body_projections"]) == 7
         and digest(exported) == digest(imported / "FactsBehaviorSupply.out")
         and wrapper.read_text() ==
         'From LeanImport Require Import Lean.\nLean Import "FactsBehaviorSupply.out".\n'
         and digest(imported_vo)
         and imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns
         and "Error:" not in (W / "merged_import.log").read_text(),
         "fresh actual-artifact export/import missing")
    controlled = V / "certificates/analysis_facts_behavior_supply"
    compiled = W / "merged_certificates"
    for name in MODULES:
        v, vo = compiled / f"{name}.v", compiled / f"{name}.vo"
        source_text = v.read_text()
        if name == "PropSPropFoundation":
            need(digest(v) == digest(V / "certificates/common/PropSPropFoundation.v")
                 and len(re.findall(r"\bAxiom\b", source_text)) == 1
                 and "Axiom interpret_strict :" in source_text
                 and not re.search(r"\b(Admitted|admit|sorry)\b", source_text),
                 "Prop/SProp foundation changed or gained an axiom")
        else:
            need(not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", source_text),
                 f"forbidden proof gap: {name}")
        need(digest(v) and digest(vo)
             and vo.stat().st_mtime_ns > v.stat().st_mtime_ns
             and "Error:" not in (compiled / f"{name}.log").read_text(),
             f"Rocq certificate invalid: {name}")
    for name in CONTROLLED:
        need(digest(compiled / f"{name}.v") == digest(controlled / f"{name}.v"),
             f"controlled certificate differs: {name}")
    assumption_config = controlled / "facts_supply_assumption_config.json"
    need(read(assumption_config)["imported_artifact_sha256"] == digest(imported_vo),
         "assumption config bound to different imported artifact")
    summary = read(W / "merged_assumption_summary.json")
    need(summary["audit_policy"] == "fail_closed"
         and set(summary["certificates"]) == set(read(assumption_config)["certificates"])
         and "AUDIT_END progress_inside_supplies"
         in (compiled / "FactsSupplyAssumptionAudit.log").read_text(),
         "assumption log missing/truncated")
    for name in NAMES:
        item = summary["certificates"][name]
        need(item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
             and item["semantic_premises"] == []
             and item["statement_only_dependencies"] == []
             and item["unexpected"] == []
             and item["prop_sprop_foundation"] ==
             ["PropSPropFoundation.interpret_strict"]
             and not item["source_theorem_dependency"]
             and not item["target_theorem_dependency"],
             f"semantic assumption gate failed: {name}")
    operation_inventory = read(W / "certificates/facts_supply_operation_inventory_audit.json")
    need(operation_inventory.get("status") == "PASS",
         "operation dependency inventory not closed")
    need(not output("git", "-C", str(ROOT), "status", "--porcelain", "--",
                    "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = V / "imported/translation_order/analysis_facts_behavior_supply"
    manifest_path = PIPE / "analysis_facts_behavior_supply_module_manifest.json"
    status_path = PIPE / "analysis_facts_behavior_supply_module_status.json"
    need(not destination.exists() and not manifest_path.exists() and not status_path.exists(),
         "already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".facts-behavior-supply-",
                                  dir=destination.parent))
    for path, name in (
        (exported, "FactsBehaviorSupply.out"),
        (wrapper, wrapper.name),
        (imported_vo, imported_vo.name),
        (source_copy, "source_compat.v"),
        (source_vo, "source_compat.vo"),
        (W / "merged_source_type_audit.log", "source_type_audit.log"),
        (lean_log, "lean_type_audit.log"),
        (W / "merged_assumption_summary.json", "assumption_summary.json"),
        (compiled / "FactsSupplyAssumptionAudit.log", "assumption_audit.log"),
        (W / "merged_reexport.log", "export.log"),
        (W / "merged_import.log", "import.log"),
    ):
        shutil.copy2(path, stage / name)
    (stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(compiled / f"{name}{suffix}",
                         stage / "certificates" / f"{name}{suffix}")
    need(digest(stage / "FactsBehaviorSupply.out") == digest(exported)
         and digest(stage / imported_vo.name) == digest(imported_vo),
         "publication stage corrupted")
    stage.rename(destination)
    artifacts = {
        "official_source": official,
        "source_compatibility_patch": patch,
        "source_compatibility_copy": destination / "source_compat.v",
        "source_vo": destination / "source_compat.vo",
        "production_source": production,
        "production_olean": olean,
        "computation_interface": interface,
        "computation_interface_olean": interface_olean,
        "lean_type_audit_source": lean_audit,
        "export_config": config_path,
        "assumption_config": assumption_config,
        "export": destination / "FactsBehaviorSupply.out",
        "imported_v": destination / wrapper.name,
        "imported_vo": destination / imported_vo.name,
        "source_type_audit": destination / "source_type_audit.log",
        "lean_type_audit": destination / "lean_type_audit.log",
        "assumption_summary": destination / "assumption_summary.json",
        "assumption_audit": destination / "assumption_audit.log",
        "operation_inventory": W / "certificates/facts_supply_operation_inventory_audit.json",
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
            "lean_declaration": f"Prosa.Analysis.Facts.Behavior.Supply.{name}",
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
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": "ANALYSIS_FACTS_BEHAVIOR_SUPPLY",
        "source_commit": PIN,
        "source_file": SOURCE,
        "source_file_sha256": digest(official),
        "source_acquisition": {
            "mode": "VERIFIED_WORKER_CACHE",
            "reason": "Rocq 9.3 main-path clean source recompile differs; cached source .vo was kernel-loaded and source types rechecked",
            "private_source_sha256": digest(private_source),
            "private_vo_sha256": digest(private_vo),
        },
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
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": len(NAMES),
            "translated": len(NAMES),
            "proof_clean": len(NAMES),
            "certified": 0,
            "certified_with_prop_sprop_foundation": len(NAMES),
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
