#!/usr/bin/env python3
"""Fail-closed publication of the pinned abstract-definitions whole file."""

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
WORK = V / ".work/experiments/analysis_abstract_definitions"
SOURCE = "analysis/abstract/definitions.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
LEAN_SHA = "95a0f43f588eecd558ee5beb77cd5358f90ee02fe7b9923819a6cf5c16f1849c"
OLEAN_SHA = "5a224be9d4dd8ba6ec7017fc351c7d50b12df516350658ab21682c85c3bef6dc"
EXPORT_SHA = "96b634874b0b13e65310749fd2c6acf4d7c11cebabac7a191f9b85796832cb1b"
IMPORT_SHA = "da34de17c5305e2c197bb98b09b22c6f225752802f95cbfa77b2a50fdc85f237"
NAMES = (
    "Interference", "InterferingWorkload", "cond_interference",
    "cumul_cond_interference", "cumulative_interference",
    "cumulative_interfering_workload", "no_speculative_execution", "quiet_time",
    "busy_interval_prefix", "busy_interval", "busy_interval_is_unique",
    "work_conserving", "busy_intervals_are_bounded_by",
    "cond_interference_is_bounded_by", "job_interference_is_bounded_by",
)
TARGET_MODULES = (
    "AbstractDefinitionsBaseAdapter", "AbstractDefinitionsClasses",
    "AbstractDefinitionsOperations", "AbstractDefinitionsNatBoolOperations",
    "AbstractDefinitionsIntervalOperations", "AbstractDefinitionsSums",
    "AbstractDefinitionsLogical", "AbstractDefinitionsPendingOperations",
    "AbstractDefinitionsArrivalOperations", "AbstractDefinitionsTaskOperations",
    "AbstractDefinitionsBusyInterval", "AbstractDefinitionsJobBound",
    "AbstractDefinitionsTypeAudit", "AbstractDefinitionsAssumptionAudit",
)
REPLAY_MODULES = (
    "ServiceBaseAdapter", "ServiceNatBoolOperations",
    "ServiceIntervalOperations", "ServiceScheduleOperations",
)


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise SystemExit("ABSTRACT_DEFINITIONS_PUBLICATION_REJECTED: " + reason)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    require(path.is_file(), f"missing {path}")
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    official_root = V / ".work/prosa-v06-414e667"
    official = official_root / SOURCE
    source_copy = WORK / "source" / SOURCE
    with (V / "planning/v06_dependency/file_inventory.csv").open() as stream:
        row = next(r for r in csv.DictReader(stream) if r["file"] == SOURCE)
    source_sha = row["sha256"]
    require(row["layer"] == "11" and sha(official) == source_sha
            and sha(source_copy) == source_sha
            and command("git", "-C", str(official_root), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(official_root), "status", "--porcelain",
                            "--untracked-files=all"), "pinned source changed")
    graph = read(V / "planning/v06_dependency/file_dag.json")
    deps = {edge["dependency_file"] for edge in graph["edges"]
            if edge["dependent_file"] == SOURCE}
    require(deps == {"model/task/concept.v"}, "authoritative file DAG changed")
    concept = read(PIPE / "model_task_concept_module_manifest.json")
    concept_olean = WORK / "olean/Prosa/Model/Task/Concept.olean"
    require(concept["acceptance"] == "ACCEPTED_V06_FILE"
            and sha(PROJECT / concept["production_file"]) ==
                concept["production_source_sha256"]
            and sha(concept_olean) == concept["production_olean_sha256"],
            "accepted Concept dependency invalidated")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    require(tuple(r["declaration_name"] for r in rows) == NAMES
            and all(r["final_type_or_type_fingerprint"].startswith("rocq-check-sha256:")
                    for r in rows), "public inventory or elaborated source evidence changed")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version")
            and command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                        "rev-parse", "HEAD") ==
                "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                                 "rocq", "--version"), "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    require(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export") ==
                tooling["lean4export"]["expected_binary_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs") ==
                tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo") ==
                tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Analysis/Abstract/Definitions.lean"
    olean = WORK / "olean/Prosa/Analysis/Abstract/Definitions.olean"
    source_vo = WORK / "source/analysis/abstract/definitions.vo"
    source_guard = V / "fixtures/translation_order/AbstractDefinitionsSourceTypeAudit.v"
    source_guard_vo = WORK / "source/AbstractDefinitionsSourceTypeAudit.vo"
    imported_v = WORK / "imported_refreeze/ImportedAbstractDefinitions.v"
    imported_vo = WORK / "imported_refreeze/ImportedAbstractDefinitions.vo"
    exported = WORK / "imported_refreeze/AbstractDefinitions.out"
    cert_dir = WORK / "certificates_refreeze"
    require(sha(production) == LEAN_SHA and sha(olean) == OLEAN_SHA
            and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
            and sha(source_vo) and source_vo.stat().st_mtime_ns > source_copy.stat().st_mtime_ns
            and sha(source_guard) == sha(WORK / "source/AbstractDefinitionsSourceTypeAudit.v")
            and sha(source_guard_vo) and source_guard_vo.stat().st_mtime_ns > source_vo.stat().st_mtime_ns
            and "Closed under the global context" in
                (WORK / "source_type_audit.log").read_text()
            and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text()),
            "source/Lean freeze or proof-clean gate failed")
    lean_log = (WORK / "lean_type_audit.log").read_text()
    allowed_lean_axioms = {"propext", "Classical.choice", "Quot.sound"}
    require("error:" not in lean_log.lower(), "Lean declaration proof-axiom audit failed")
    for name in NAMES:
        qualified = "Prosa.Analysis.Abstract.Definitions." + name
        matches = re.findall(
            rf"'{re.escape(qualified)}' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
            lean_log,
        )
        require(len(matches) == 1, f"missing/ambiguous Lean proof-axiom output: {name}")
        listed = matches[0][1]
        actual_axioms = {part.strip() for part in listed.split(",") if part.strip()}
        require(actual_axioms <= allowed_lean_axioms,
                f"unexpected Lean proof axiom for {name}: {sorted(actual_axioms - allowed_lean_axioms)}")
    config = V / "tooling/analysis_abstract_definitions_export_config.json"
    export_meta = read(WORK / "export_refreeze_metadata.json")
    require(export_meta["config_sha256"] == sha(config)
            and export_meta["output_sha256"] == EXPORT_SHA
            and export_meta["statement_only_count"] == 1
            and sha(exported) == EXPORT_SHA and sha(imported_vo) == IMPORT_SHA
            and imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns
            and 'Lean Import "AbstractDefinitions.out"' in imported_v.read_text()
            and (WORK / "export_refreeze.log").read_text().count("kernel_rfl_guard=true") == 7
            and "kernel_rfl_guard=false" not in
                (WORK / "export_refreeze.log").read_text(),
            "actual compiled export/import or guarded projection changed")
    for fixture in ("ServiceComputationInterface", "AbstractDefinitionsComputationInterface"):
        src = V / f"fixtures/translation_order/{fixture}.lean"
        artifact = WORK / f"olean/Validation/fixtures/translation_order/{fixture}.olean"
        require(sha(src) and sha(artifact)
                and artifact.stat().st_mtime_ns > src.stat().st_mtime_ns,
                f"computation guard not freshly compiled: {fixture}")
    all_modules = TARGET_MODULES + REPLAY_MODULES
    for name in all_modules:
        root = (V / "certificates/analysis_abstract_definitions"
                if name in TARGET_MODULES else cert_dir)
        formal = root / f"{name}.v"
        copy = cert_dir / f"{name}.v"
        compiled = cert_dir / f"{name}.vo"
        require(sha(formal) == sha(copy) and sha(compiled)
                and compiled.stat().st_mtime_ns > copy.stat().st_mtime_ns
                and compiled.stat().st_mtime_ns > imported_vo.stat().st_mtime_ns
                and not re.search(r"\b(Axiom|Admitted|admit|sorry)\b", formal.read_text()),
                f"certificate stale or contains forbidden proof gap: {name}")
    audit_log = WORK / "AbstractDefinitionsAssumptionAudit.log"
    summary = read(WORK / "assumption_summary.json")
    require(summary.get("audit_policy") == "fail_closed"
            and "AUDIT_END job_interference_is_bounded_by" in audit_log.read_text(),
            "assumption audit missing/truncated")
    require(set(NAMES).issubset(summary.get("certificates", {})),
            "one or more target audit entries missing")
    for name in NAMES:
        item = summary["certificates"][name]
        require(item["status"] in {"CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"]
                and item["prop_sprop_foundation"] ==
                    (["PropSPropFoundation.interpret_strict"]
                     if item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" else []),
                f"semantic audit gate failed: {name}")
    proof = (V / "certificates/analysis_abstract_definitions/AbstractDefinitionsBusyInterval.v").read_text()
    start = proof.index("Lemma ad_busy_interval_unique_statement_correspondence")
    end = proof.index("Qed.", start)
    require("busy_interval_is_unique" not in proof[start:end]
            and "ad_busy_interval_correspondence" in proof[start:end],
            "busy_interval theorem proof uses source/target theorem itself")
    require(not command("git", "-C", str(ROOT), "status", "--porcelain", "--",
                        "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    candidates = []
    for path in PIPE.glob("*_module_status.json"):
        state = read(path)
        if state.get("status") == "PASS":
            coverage = state.get("coverage", {})
            candidates.append((coverage.get("accepted_files", -1),
                               coverage.get("accepted_declarations", -1), path))
    require(bool(candidates), "no cumulative PASS status")
    previous_files, previous_decls, previous_path = max(candidates)
    require(sum(x[:2] == (previous_files, previous_decls) for x in candidates) == 1
            and (previous_files, previous_decls) >= (66, 463),
            "latest accepted baseline missing or ambiguous")
    previous = read(previous_path)
    destination = V / "imported/translation_order/abstract_definitions"
    manifest_path = PIPE / "analysis_abstract_definitions_module_manifest.json"
    status_path = PIPE / "analysis_abstract_definitions_module_status.json"
    require(not destination.exists() and not manifest_path.exists()
            and not status_path.exists(), "already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    staged = Path(tempfile.mkdtemp(prefix=".abstract-definitions-", dir=destination.parent))
    evidence = {
        "source_vo": source_vo, "source_type_guard_vo": source_guard_vo,
        "production_olean": olean, "export": exported,
        "imported_v": imported_v, "imported_vo": imported_vo,
        "assumption_summary": WORK / "assumption_summary.json",
        "assumption_log": audit_log, "lean_axiom_audit_log": WORK / "lean_type_audit.log",
        "export_metadata": WORK / "export_refreeze_metadata.json",
    }
    for key, original in list(evidence.items()):
        target = staged / (key + original.suffix)
        shutil.copy2(original, target)
        require(sha(target) == sha(original), f"publication copy corrupted: {key}")
        evidence[key] = target
    (staged / "certificates").mkdir()
    for name in all_modules:
        for suffix in (".v", ".vo"):
            original = cert_dir / (name + suffix)
            target = staged / "certificates" / original.name
            shutil.copy2(original, target)
            require(sha(target) == sha(original), f"certificate copy corrupted: {name}")
            evidence[name + suffix] = target
    staged.rename(destination)
    evidence = {key: destination / path.relative_to(staged)
                for key, path in evidence.items()}
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        item = summary["certificates"][name]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Analysis.Abstract.Definitions." + name,
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_fingerprint": row["final_type_or_type_fingerprint"],
            "semantic_certificate": item["certificate"],
            "semantic_status": item["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation": item["prop_sprop_foundation"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": "ANALYSIS_ABSTRACT_DEFINITIONS", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": source_sha,
        "direct_file_dependencies": sorted(deps),
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "validation_mode": "FILE_VALIDATE_WITH_VERIFIED_ACCEPTED_PRODUCERS",
        "target_build": "FRESH", "export": "FRESH", "rocq_import": "FRESH",
        "acceptance": "ACCEPTED_V06_FILE", "declarations": declarations,
        "artifact_hashes": {key + "_sha256": sha(path) for key, path in evidence.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT)) for key, path in evidence.items()},
        "export_config_sha256": sha(config),
        "tooling_manifest_sha256": sha(V / "tooling/tooling_manifest.json"),
        "previous_status_file": previous_path.name,
        "previous_status_sha256": sha(previous_path),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = {**previous["coverage"],
                "accepted_files": previous_files + 1,
                "accepted_declarations": previous_decls + 15}
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 15, "translated": 15, "proof_clean": 15,
            "certified": sum(d["semantic_status"] == "CERTIFIED" for d in declarations),
            "certified_with_prop_sprop_foundation":
                sum(d["semantic_status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                    for d in declarations),
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": coverage, "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "coverage": coverage}, sort_keys=True))


if __name__ == "__main__":
    main()
