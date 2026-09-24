#!/usr/bin/env python3
"""Fail-closed publication for the pinned restricted-supply whole-file slice."""

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
VALIDATION = PROJECT / "Validation"
WORK = VALIDATION / ".work/experiments/model_processor_restricted_supply"
PIPE = VALIDATION / "planning/v06_pipeline"
SOURCE_FILE = "model/processor/restricted_supply.v"
SOURCE_COMMIT = "414e66760333eaa4ef78c685bcf53291c527a548"
LEAN_MODULE = "Prosa.Model.Processor.RestrictedSupply"
NAMES = (
    "processor_state", "rs_scheduled_on", "rs_supply_on", "rs_service_on",
    "rs_processor_state",
)
CERTIFICATES = (
    "rs_state_type_correspondence", "rs_scheduled_on_correspondence",
    "rs_supply_on_correspondence", "rs_service_on_correspondence",
    "rs_processor_state_correspondence",
)
PROP_TARGETS = {"rs_scheduled_on", "rs_service_on", "rs_processor_state"}


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise SystemExit(f"RESTRICTED_SUPPLY_PUBLICATION_REJECTED: {reason}")


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    require(path.is_file(), f"missing {path}")
    return json.loads(path.read_text())


def cmd(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = load(PIPE / "model_processor_restricted_supply_selection.json")
    baseline = load(PIPE / "model_processor_platform_properties_module_status.json")
    require(selection["rank"] == 52 and selection["layer"] == 10
            and selection["source_file"] == SOURCE_FILE
            and selection["source_commit"] == SOURCE_COMMIT
            and selection["file_dag_ready"]
            and selection["direct_internal_dependencies"] == ["behavior/all.v"]
            and selection["targets_in_source_order"] == list(NAMES),
            "selection/DAG/inventory mismatch")
    require(baseline["status"] == "PASS"
            and baseline["coverage"]["accepted_files"] == 49
            and baseline["coverage"]["accepted_declarations"] == 359,
            "baseline changed")

    pinned = VALIDATION / ".work/prosa-v06-414e667"
    official = pinned / SOURCE_FILE
    source_copy = WORK / "source" / SOURCE_FILE
    require(cmd("git", "-C", str(pinned), "rev-parse", "HEAD") == SOURCE_COMMIT
            and cmd("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}")
            == "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
            and not cmd("git", "-C", str(pinned), "status", "--porcelain",
                        "--untracked-files=all")
            and sha(official) == selection["source_sha256"],
            "authoritative source not clean/pinned")
    old = "  Next Obligation. by move=> j s r; case s, r => //=; case: (_ == _). Qed."
    new_first = "  Next Obligation. by case: s => [|j'|j'|] //=; case: (_ == _). Qed."
    new_second = "  Next Obligation. by move: H; case: s => [|j'|j'|] //=; case: (_ == _). Qed."
    source_text = official.read_text()
    require(source_text.count(old) == 2 and source_copy.read_text() ==
            source_text.replace(old, new_first, 1).replace(old, new_second, 1),
            "Rocq 9.3 validation copy changed public source content")
    patch = VALIDATION / "patches/prosa-v06-rocq93-model-processor-restricted-supply.patch"
    require(sha(patch), "compatibility patch missing")
    source_vo = source_copy.with_suffix(".vo")
    require(sha(source_vo) and source_vo.stat().st_mtime_ns > source_copy.stat().st_mtime_ns,
            "source compile stale")
    source_type_log = WORK / "source_type_audit.log"
    source_types = source_type_log.read_text()
    require("Error:" not in source_types and all(name in source_types for name in NAMES),
            "source elaborated type audit incomplete")
    with (VALIDATION / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream) if row["source_file"] == SOURCE_FILE]
    require([row["declaration_name"] for row in rows] == list(NAMES),
            "source public inventory changed")
    types = load(VALIDATION / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + types[row["qualified_name"]]["sha256"],
                f"source final-type fingerprint changed: {row['declaration_name']}")

    dep_manifest = load(PIPE / "behavior_all_module_manifest.json")
    dep_status = load(PIPE / "behavior_all_module_status.json")
    platform_manifest = load(PIPE / "model_processor_platform_properties_module_manifest.json")
    require(dep_manifest["acceptance"] == "ACCEPTED_V06_FILE"
            and dep_status["status"] == "PASS"
            and platform_manifest["acceptance"] == "ACCEPTED_V06_FILE"
            and sha(PROJECT / dep_manifest["production_file"])
            == dep_manifest["production_source_sha256"],
            "accepted dependency producer changed")
    olean_dir = WORK / "olean"
    predecessor = VALIDATION / ".work/experiments/model_processor_platform_properties/olean"
    dep_relative = "Prosa/Behavior/All.olean"
    require(sha(olean_dir / dep_relative) ==
            dep_manifest["production_olean_sha256"]
            == sha(predecessor / dep_relative), "dependency artifact differs")
    for artifact in predecessor.glob("Prosa/**/*.olean"):
        relative = artifact.relative_to(predecessor)
        require(sha(olean_dir / relative) == sha(artifact),
                f"copied accepted build closure changed: {relative}")

    require("Lean (version 4.33.1" in cmd("lake", "env", "lean", "--version")
            and cmd("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in cmd("opam", "exec", "--switch=rocq93rc1",
                             "--", "rocq", "--version"),
            "toolchain changed")
    tooling = load(VALIDATION / "tooling/tooling_manifest.json")
    require(sha(VALIDATION / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Model/Processor/RestrictedSupply.lean"
    target_olean = olean_dir / "Prosa/Model/Processor/RestrictedSupply.olean"
    require(sha(production) and sha(target_olean)
            and target_olean.stat().st_mtime_ns > production.stat().st_mtime_ns,
            "compiled Lean target stale")
    lean_audit_file = WORK / "lean_audit.log"
    lean_audit = lean_audit_file.read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit
            and all(f"{LEAN_MODULE}.{name}" in lean_audit for name in NAMES),
            "Lean type/axiom audit incomplete")
    for name in NAMES[:-1]:
        require(f"'{LEAN_MODULE}.{name}' does not depend on any axioms" in lean_audit,
                f"unexpected Lean axiom: {name}")
    require(f"'{LEAN_MODULE}.rs_processor_state' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]" in lean_audit,
            "class axiom set changed")
    require(not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text()),
            "forbidden production escape")

    export_config = VALIDATION / "tooling/model_processor_restricted_supply_export_config.json"
    config = load(export_config)
    export = WORK / "RestrictedSupplyFull.out"
    export_meta = load(WORK / "export_full_metadata.json")
    portable = WORK / "portable"
    imported = portable / "imported"
    cert_dir = portable / "certificates"
    imported_v = imported / "ImportedRestrictedSupplyFull.v"
    imported_vo = imported / "ImportedRestrictedSupplyFull.vo"
    require(config["module"] == LEAN_MODULE
            and config["targets"] == [f"{LEAN_MODULE}.{name}" for name in NAMES]
            and config["statement_only"] == []
            and config["normalization"] == {
                "theorem_types": [], "subexpression_heads": [],
                "definition_bodies": [], "body_projections": []}
            and export_meta["config_sha256"] == sha(export_config)
            and export_meta["output_sha256"] == sha(export)
            and sha(imported / export.name) == sha(export)
            and 'Lean Import "RestrictedSupplyFull.out".' in imported_v.read_text()
            and sha(imported_vo),
            "actual imported artifact/config mismatch")
    budget = load(WORK / "dependency_budget_full.json")
    require(budget["export_sha256"] == sha(export)
            and budget["explicit_export_root_count"] == len(NAMES),
            "dependency-budget evidence stale")

    modules = ("RestrictedSupplyBaseAdapter", "RestrictedSupplyCorrespondence",
               "RestrictedSupplyExactTypeGuards", "RestrictedSupplyAssumptionAudit")
    for module in modules:
        controlled = VALIDATION / f"certificates/model_processor_restricted_supply/{module}.v"
        copied = cert_dir / f"{module}.v"
        compiled = cert_dir / f"{module}.vo"
        require(sha(controlled) == sha(copied) and sha(compiled),
                f"certificate copy/compile stale: {module}")
        require(not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", copied.read_text()),
                f"forbidden Rocq escape: {module}")
    adapter_meta = load(WORK / "adapter_metadata.json")
    require(adapter_meta["imported_artifact_sha256"] == sha(export)
            and adapter_meta["output_sha256"] == sha(cert_dir / "RestrictedSupplyBaseAdapter.v")
            and adapter_meta["semantic_assumptions_added"] == [],
            "artifact-local adapter not bound")
    summary = load(WORK / "portable_assumption_summary.json")
    assumption_log = WORK / "portable_assumption.log"
    require(summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(NAMES)
            and sha(assumption_log), "assumption audit incomplete")
    for name in NAMES:
        item = summary["certificates"][name]
        expected = ("CERTIFIED_WITH_PROP_SPROP_FOUNDATION" if name in PROP_TARGETS
                    else "CERTIFIED")
        require(item["status"] == expected
                and item["certificate"] == CERTIFICATES[NAMES.index(name)]
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"],
                f"semantic assumption gate failed: {name}")
    require(not cmd("git", "-C", str(PROJECT.parent), "status", "--porcelain",
                    "--", "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(PROJECT.parent), "diff", "--check"], check=True)

    output = VALIDATION / "imported/translation_order/restricted_supply"
    require(not output.exists(), "publication directory already exists")
    output.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".restricted_supply.", dir=output.parent))
    for source in (imported / export.name, imported_v, imported_vo,
                   WORK / "export_full_metadata.json", WORK / "dependency_budget_full.json",
                   WORK / "portable_assumption.log", WORK / "portable_assumption_summary.json",
                   lean_audit_file, source_type_log, WORK / "adapter_metadata.json"):
        shutil.copy2(source, staging / source.name)
    (staging / "certificates").mkdir()
    for module in modules:
        for suffix in (".v", ".vo"):
            source = cert_dir / f"{module}{suffix}"
            shutil.copy2(source, staging / "certificates" / source.name)
    require(sha(staging / export.name) == sha(export)
            and sha(staging / imported_vo.name) == sha(imported_vo),
            "staged artifact corrupt")
    staging.rename(output)

    artifacts = {
        "official_source": official,
        "compatibility_patch": patch,
        "validation_source": source_copy,
        "source_vo": source_vo,
        "source_type_log": output / source_type_log.name,
        "production_source": production,
        "production_olean": target_olean,
        "lean_audit": output / lean_audit_file.name,
        "export_config": export_config,
        "export": output / export.name,
        "imported_v": output / imported_v.name,
        "imported_vo": output / imported_vo.name,
        "adapter_metadata": output / "adapter_metadata.json",
        "certificate_v": VALIDATION / "certificates/model_processor_restricted_supply/RestrictedSupplyCorrespondence.v",
        "certificate_vo": output / "certificates/RestrictedSupplyCorrespondence.vo",
        "exact_type_guard_v": VALIDATION / "certificates/model_processor_restricted_supply/RestrictedSupplyExactTypeGuards.v",
        "exact_type_guard_vo": output / "certificates/RestrictedSupplyExactTypeGuards.vo",
        "assumption_log": output / "portable_assumption.log",
        "assumption_summary": output / "portable_assumption_summary.json",
        "dependency_budget": output / "dependency_budget_full.json",
    }
    declarations = []
    for row, cert in zip(rows, CERTIFICATES, strict=True):
        name = row["declaration_name"]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": types[row["qualified_name"]]["sha256"],
            "kind": row["kind"],
            "lean_declaration": f"{LEAN_MODULE}.{name}",
            "semantic_certificate": cert,
            "semantic_status": summary["certificates"][name]["status"],
            "prop_sprop_foundation": (["PropSPropFoundation.interpret_strict"]
                                      if name in PROP_TARGETS else []),
            "semantic_premises": [],
            "statement_only_dependencies": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "source_file": SOURCE_FILE,
        "source_commit": SOURCE_COMMIT,
        "rank": 52,
        "acceptance": "ACCEPTED_V06_FILE",
        "build_mode": "FILE_VALIDATE",
        "dependency_reuse": "VERIFIED_CACHE_FROM_ACCEPTED_PLATFORM_PROPERTIES",
        "target_build": "FRESH",
        "source_acquisition": "PINNED_SOURCE_WITH_PROOF_SCRIPT_ONLY_ROCQ93_PATCH",
        "translation_file": str(production.relative_to(PROJECT)),
        "proof_clean": True,
        "actual_compiled_artifact_imported": True,
        "declarations": declarations,
        "artifact_hashes": {key: sha(value) for key, value in artifacts.items()},
        "artifact_paths": {key: str(value.relative_to(PROJECT))
                           for key, value in artifacts.items()},
        "accepted_dependency_manifest_sha256": {
            "behavior_all": sha(PIPE / "behavior_all_module_manifest.json"),
            "platform_properties_producer": sha(PIPE / "model_processor_platform_properties_module_manifest.json"),
        },
        "tooling_manifest_sha256": sha(VALIDATION / "tooling/tooling_manifest.json"),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_file = PIPE / "model_processor_restricted_supply_module_manifest.json"
    manifest_file.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = dict(baseline["coverage"])
    coverage["accepted_files"] += 1
    coverage["accepted_declarations"] += len(NAMES)
    status = {
        "slice": "MODEL_PROCESSOR_RESTRICTED_SUPPLY",
        "status": "PASS",
        "manifest_sha256": sha(manifest_file),
        "coverage": coverage,
        "per_file": {SOURCE_FILE: {
            "status": "ACCEPTED_V06_FILE",
            "public_declarations": len(NAMES),
            "translated": len(NAMES),
            "proof_clean": len(NAMES),
            "certified": len(NAMES),
            "certified_with_prop_sprop_foundation": len(PROP_TARGETS),
        }},
    }
    status_file = PIPE / "model_processor_restricted_supply_module_status.json"
    status_file.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "accepted_files": coverage["accepted_files"],
                      "accepted_declarations": coverage["accepted_declarations"],
                      "published": str(output)}, sort_keys=True))


if __name__ == "__main__":
    main()
