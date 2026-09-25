#!/usr/bin/env python3
"""Fail-closed publication of Rank 68 against the fresh main-tree artifact."""

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
W = V / ".work/experiments/analysis_facts_model_restricted_supply_schedule"
SOURCE = "analysis/facts/model/restricted_supply/schedule.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
NAMES = (
    "rs_proc_model_is_a_uniprocessor_model",
    "rs_proc_is_unit_supply",
    "rs_proc_model_fully_consuming",
)
MODULES = (
    "PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence",
    "RestrictedSupplyScheduleSourceComputation",
    "RestrictedSupplyScheduleBaseAdapter",
    "RestrictedSupplyScheduleStateCorrespondence",
    "RestrictedSupplyScheduleOperations",
    "RestrictedSupplyScheduleModelCorrespondence",
    "RestrictedSupplyScheduleExactTypeGuards",
    "RestrictedSupplyScheduleAssumptionAudit",
)


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise SystemExit("RESTRICTED_SUPPLY_SCHEDULE_PUBLICATION_REJECTED: " + reason)


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
    last = max(candidates)
    require(sum(item[:2] == last[:2] for item in candidates) == 1,
            "ambiguous cumulative status")
    require(last[0] >= 63 and last[1] >= 454,
            "Rank 63 accepted baseline missing")
    return last[2], read(last[2])


def accepted_manifest_corpus() -> list[str]:
    corpus = []
    legacy = {
        "foundation_slice_1_manifest.json": "FOUNDATION_SLICE_1_STATUS",
        "foundation_slice_2_closure_manifest.json": "FOUNDATION_SLICE_2_CLOSURE_STATUS",
        "utility_foundation_expansion_manifest.json": "UTILITY_FOUNDATION_EXPANSION_STATUS",
    }
    for path in PIPE.glob("*manifest.json"):
        status_path = path.with_name(path.name.replace("manifest.json", "status.json"))
        if not status_path.is_file():
            continue
        manifest, status = read(path), read(status_path)
        if ((manifest.get("acceptance") == "ACCEPTED_V06_FILE"
             and status.get("status") == "PASS")
                or (path.name in legacy
                    and status.get(legacy[path.name]) == "PASS")):
            corpus.append(path.read_text())
    require(len(corpus) >= 50, "accepted manifest corpus incomplete")
    return corpus


def main() -> None:
    previous_path, previous = latest_status()
    official_root = V / ".work/prosa-v06-414e667"
    official = official_root / SOURCE
    patched = W / "source_compat" / SOURCE
    source_vo = patched.with_suffix(".vo")
    source_probe = W / "source_compat/SourceTypeProbe.v"
    source_probe_log = W / "source_type_probe.log"
    patch = V / "patches/prosa-v06-rocq93-analysis-facts-model-restricted-supply-schedule.patch"
    require(output("git", "-C", str(official_root), "rev-parse", "HEAD") == PIN
            and output("git", "-C", str(official_root), "rev-parse", "HEAD^{tree}") == TREE
            and not output("git", "-C", str(official_root), "status", "--porcelain",
                           "--untracked-files=all"), "official v0.6 checkout changed")
    require(sha(official) == "0e7bbb5656f05d8886d62b76a2fdc168a03404dbfc798fe18d8d1777b91cbb75"
            and sha(patch) == "bc76e7d8fb82aaa069ba647eeec969727b64a951c0590cd410b326127b7bb443"
            and source_vo.stat().st_mtime_ns > patched.stat().st_mtime_ns,
            "official source or proof-only Rocq 9.3 compatibility changed")
    original_lines, patched_lines = official.read_text().splitlines(), patched.read_text().splitlines()
    insertion_end = len(patched_lines) - len(original_lines) + 2
    require(insertion_end == 14
            and patched_lines[:2] == original_lines[:2]
            and patched_lines[insertion_end:] == original_lines[2:]
            and "Local Lemma sum_unit1" in "\n".join(patched_lines[2:insertion_end]),
            "compatibility patch changed any original source declaration text")
    with (V / "planning/v06_dependency/file_inventory.csv").open() as stream:
        file_row = next(row for row in csv.DictReader(stream) if row["file"] == SOURCE)
    require(file_row["sha256"] == sha(official) and file_row["layer"] == "11",
            "authoritative file inventory changed")
    graph = read(V / "planning/v06_dependency/file_dag.json")
    deps = {edge["dependency_file"] for edge in graph["edges"]
            if edge["dependent_file"] == SOURCE}
    require(deps == {"model/processor/platform_properties.v",
                     "model/processor/restricted_supply.v"}, "file DAG changed")
    for stem in ("model_processor_platform_properties", "model_processor_restricted_supply"):
        manifest_path = PIPE / f"{stem}_module_manifest.json"
        manifest, status = read(manifest_path), read(PIPE / f"{stem}_module_status.json")
        require(manifest["acceptance"] == "ACCEPTED_V06_FILE"
                and status["status"] == "PASS"
                and sha(PROJECT / manifest["artifact_paths"]["production_source"])
                == manifest["artifact_hashes"]["production_source"],
                f"accepted file dependency changed: {stem}")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream) if row["source_file"] == SOURCE]
    type_evidence = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    require([row["declaration_name"] for row in rows] == list(NAMES)
            and all(row["kind"] == "Lemma" and
                    row["final_type_or_type_fingerprint"] ==
                    "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"]
                    for row in rows), "source public declaration/type inventory changed")
    probe_log = source_probe_log.read_text()
    require(sha(source_probe) and all("@" + name in probe_log for name in NAMES)
            and "Error:" not in probe_log,
            "official elaborated Rocq type probe missing")

    require("Lean (version 4.33.1" in output("lean", "--version")
            and output("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                       "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in output("opam", "exec", "--switch=rocq93rc1",
                                "--", "rocq", "--version"), "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    require(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")
    stage = read(W / "accepted_artifact_stage.json")
    for stem, key in (("model_processor_platform_properties", "platform_manifest_sha256"),
                      ("model_processor_restricted_supply", "restricted_manifest_sha256")):
        require(stage[key] == sha(PIPE / f"{stem}_module_manifest.json"),
                f"accepted producer manifest changed: {stem}")
    olean_root = W / "olean"
    for relative, expected in stage["copied"][".olean"].items():
        artifact = olean_root / "Prosa" / relative
        dep_source = PROJECT / "Prosa" / Path(relative).with_suffix(".lean")
        corpus = accepted_manifest_corpus()
        require(sha(artifact) == expected
                and any(expected in text and sha(dep_source) in text for text in corpus),
                f"accepted Lean dependency/source pair changed: {relative}")
    require(len(stage["copied"][".olean"]) == 30
            and len(stage["copied"][".vo"]) == 12,
            "accepted dependency closure size changed")
    for relative, expected in stage["copied"][".vo"].items():
        require(sha(W / "source" / relative) == expected,
                f"accepted Rocq dependency changed: {relative}")

    production = PROJECT / "Prosa/Analysis/Facts/Model/RestrictedSupply/Schedule.lean"
    olean = olean_root / "Prosa/Analysis/Facts/Model/RestrictedSupply/Schedule.olean"
    interface = V / "fixtures/translation_order/RestrictedSupplyScheduleComputationInterface.lean"
    interface_olean = olean_root / "Validation/fixtures/translation_order/RestrictedSupplyScheduleComputationInterface.olean"
    lean_probe = V / "fixtures/translation_order/RestrictedSupplyScheduleLeanTypeAudit.lean"
    lean_probe_olean = olean_root / "Validation/fixtures/translation_order/RestrictedSupplyScheduleLeanTypeAudit.olean"
    for source, artifact in ((production, olean), (interface, interface_olean),
                             (lean_probe, lean_probe_olean)):
        require(sha(source) and sha(artifact)
                and artifact.stat().st_mtime_ns > source.stat().st_mtime_ns
                and not re.search(r"\b(sorry|axiom|unsafe)\b", source.read_text()),
                f"Lean proof/build not clean: {source}")
    require(sha(production) == "61ba092fc58570007859678fb48c14a93ac6c46cdc4fbf7f927a9a44bae64475"
            and sha(olean) == "df3a964a95f54419dd5a39a866d98e8d626d1dd4a0e7cbe86ac073c5ff188f63"
            and sha(interface_olean) == "8cceaa57d0d31e571c04b1a6604d08b7bfea2f529f98950ba3314d87c6be86ff",
            "merged Lean artifact differs from frozen production snapshot")
    lean_log = (W / "lean_axiom_audit.log").read_text()
    require("sorryAx" not in lean_log and "error:" not in lean_log.lower(),
            "Lean axiom/type audit failed")
    for name in NAMES:
        match = re.search(r"'Prosa\.Analysis\.Facts\.Model\.RestrictedSupply\.Schedule\." +
                          name + r"' depends on axioms: \[([^\]]*)\]", lean_log, re.S)
        require(bool(match), f"Lean target theorem #print axioms missing: {name}")
        require(set(re.split(r",\s*", match.group(1).strip())) <=
                {"propext", "Classical.choice", "Quot.sound"},
                f"unexpected Lean axiom: {name}")

    controlled = V / "certificates/analysis_facts_model_restricted_supply_schedule"
    export_config = controlled / "export_config.json"
    config = read(export_config)
    exported = W / "imported/RestrictedSupplySchedule.out"
    imported_v = W / "imported/ImportedRestrictedSupplySchedule.v"
    imported_vo = W / "imported/ImportedRestrictedSupplySchedule.vo"
    require(config["statement_only"] ==
            ["Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule." + name for name in NAMES]
            and len(config["body_theorems"]) == 6
            and sha(exported) == "e643679ef688b800e567439db8a8b57a15e7b9b7ac57ecb58eeb5cb22fbd1dea"
            and sha(imported_v) and sha(imported_vo)
            and imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns
            and "Error:" not in (W / "export.log").read_text()
            and "Error:" not in (W / "import.log").read_text(),
            "actual compiled theorem-type/definition export or import invalid")
    require(sha(W / "imported/Subadditivity.out") in
            "\n".join(accepted_manifest_corpus()),
            "Subadditivity foundation export not accepted")
    cert_dir = W / "certificates"
    for name in MODULES:
        source = (V / "certificates/common" / f"{name}.v") if name in MODULES[:3] \
                 else (controlled / f"{name}.v")
        proof = cert_dir / f"{name}.v"
        vo = cert_dir / f"{name}.vo"
        body = proof.read_text()
        require(sha(source) == sha(proof) and sha(vo)
                and vo.stat().st_mtime_ns > proof.stat().st_mtime_ns
                and "Error:" not in (W / f"{name}.log").read_text(),
                f"controlled Rocq proof not compiled: {name}")
        if name == "PropSPropFoundation":
            require(len(re.findall(r"\bAxiom\b", body)) == 1
                    and "Axiom interpret_strict :" in body,
                    "Prop/SProp foundation changed")
        else:
            require(not re.search(r"\b(Axiom|Admitted|admit|sorry)\b", body),
                    f"forbidden Rocq proof gap: {name}")
    for name in MODULES[3:]:
        require((cert_dir / f"{name}.vo").stat().st_mtime_ns > imported_vo.stat().st_mtime_ns,
                f"certificate predates fresh imported artifact: {name}")
    assumption_config = controlled / "restricted_supply_schedule_assumption_config.json"
    summary = read(W / "assumption_summary.json")
    require(read(assumption_config)["imported_artifact_sha256"] == sha(imported_vo)
            and summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(NAMES)
            and "AUDIT_END rs_proc_model_fully_consuming" in
            (W / "RestrictedSupplyScheduleAssumptionAudit.log").read_text(),
            "fail-closed assumption audit missing/stale")
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
                f"correspondence dependency closure failed: {name}")
    operation_inventory = read(controlled / "operation_inventory.json")
    require(operation_inventory["public_declarations"] == list(NAMES)
            and operation_inventory["source_sha256"] == sha(official),
            "operation inventory not bound to pinned source")
    require(not output("git", "-C", str(ROOT), "status", "--porcelain", "--",
                       "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = V / "imported/translation_order/analysis_facts_model_restricted_supply_schedule"
    manifest_path = PIPE / "analysis_facts_model_restricted_supply_schedule_module_manifest.json"
    status_path = PIPE / "analysis_facts_model_restricted_supply_schedule_module_status.json"
    require(not destination.exists() and not manifest_path.exists()
            and not status_path.exists(), "Rank 68 already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    publication_stage = Path(tempfile.mkdtemp(prefix=".restricted-supply-schedule-",
                                               dir=destination.parent))
    artifacts = {
        "official_source": official, "patched_source": patched,
        "source_vo": source_vo, "compatibility_patch": patch,
        "source_type_probe": source_probe, "source_type_probe_log": source_probe_log,
        "production_source": production, "production_olean": olean,
        "computation_interface": interface, "computation_interface_olean": interface_olean,
        "lean_type_probe": lean_probe, "lean_type_probe_olean": lean_probe_olean,
        "lean_axiom_audit_log": W / "lean_axiom_audit.log",
        "export_config": export_config, "export": exported,
        "imported_v": imported_v, "imported_vo": imported_vo,
        "assumption_config": assumption_config,
        "assumption_summary": W / "assumption_summary.json",
        "assumption_log": W / "RestrictedSupplyScheduleAssumptionAudit.log",
        "dependency_stage": W / "accepted_artifact_stage.json",
        "operation_inventory": controlled / "operation_inventory.json",
    }
    for key in ("patched_source", "source_vo", "source_type_probe_log",
                "lean_axiom_audit_log", "export", "imported_v", "imported_vo",
                "assumption_summary", "assumption_log", "dependency_stage"):
        source = artifacts[key]
        target = publication_stage / (key + source.suffix)
        shutil.copy2(source, target)
        artifacts[key] = target
    (publication_stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            source = cert_dir / f"{name}{suffix}"
            target = publication_stage / "certificates" / source.name
            shutil.copy2(source, target)
            artifacts[f"{name}{suffix}"] = target
    require(sha(publication_stage / "imported_vo.vo") == sha(imported_vo)
            and sha(publication_stage / "export.out") == sha(exported),
            "publication stage corrupted")
    publication_stage.rename(destination)
    artifacts = {key: destination / path.relative_to(publication_stage)
                 if path.is_relative_to(publication_stage) else path
                 for key, path in artifacts.items()}
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        item = summary["certificates"][name]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule." + name,
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": item["certificate"],
            "semantic_status": item["status"],
            "target_theorem_statement_export": "EXACT_COMPILED_TYPE_ONLY",
            "semantic_premises": [], "statement_only_dependencies": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": "ANALYSIS_FACTS_MODEL_RESTRICTED_SUPPLY_SCHEDULE",
        "source_commit": PIN, "source_file": SOURCE,
        "source_file_sha256": sha(official),
        "source_acquisition": {"mode": "FRESH",
                               "proof_only_compat_patch_sha256": sha(patch)},
        "direct_file_dependencies": sorted(deps),
        "verified_accepted_dependency_oleans": 30,
        "verified_accepted_dependency_source_vos": 12,
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "validation_mode": "FILE_VALIDATE_WITH_VERIFIED_ACCEPTED_PRODUCERS",
        "target_build": "FRESH", "export": "FRESH", "rocq_import": "FRESH",
        "acceptance": "ACCEPTED_V06_FILE", "declarations": declarations,
        "artifact_hashes": {key + "_sha256": sha(path) for key, path in artifacts.items()},
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
                "accepted_declarations": previous["coverage"]["accepted_declarations"] + 3}
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 3, "translated": 3, "proof_clean": 3,
            "certified": 0, "certified_with_prop_sprop_foundation": 3,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": coverage, "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "coverage": coverage}, sort_keys=True))


if __name__ == "__main__":
    main()
