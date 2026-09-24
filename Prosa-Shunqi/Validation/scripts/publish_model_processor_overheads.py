#!/usr/bin/env python3
"""Fail-closed publication of the pinned, actual-artifact Overheads file."""

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
WORK = VALIDATION / ".work/experiments/model_processor_overheads"
PIPE = VALIDATION / "planning/v06_pipeline"
SOURCE_FILE = "model/processor/overheads.v"
SOURCE_COMMIT = "414e66760333eaa4ef78c685bcf53291c527a548"
LEAN_MODULE = "Prosa.Model.Processor.Overheads"
NAMES = (
    "proc_state", "overheads_scheduled_on", "overheads_supply_on",
    "overheads_service_on", "processor_state", "scheduled_job",
    "is_progress", "is_context_switch", "is_dispatch", "is_CRPD",
    "total_time_in_dispatch", "total_time_in_context_switch",
    "total_time_in_CRPD",
)
CERTIFICATES = (
    "ovh_state_target_roundtrip", "ovh_scheduled_on_correspondence",
    "ovh_supply_on_correspondence", "ovh_service_on_correspondence",
    "ovh_processor_state_correspondence", "ovh_scheduled_job_correspondence",
    "ovh_is_progress_correspondence", "ovh_is_context_switch_correspondence",
    "ovh_is_dispatch_correspondence", "ovh_is_CRPD_correspondence",
    "ovh_total_time_in_dispatch_correspondence",
    "ovh_total_time_in_context_switch_correspondence",
    "ovh_total_time_in_CRPD_correspondence",
)
PROP_TARGETS = {
    "overheads_scheduled_on", "overheads_service_on", "processor_state"
}
MODULES = (
    "OverheadsBaseAdapter", "OverheadsNatBoolOperations",
    "OverheadsIntervalOperations", "OverheadsCorrespondence",
    "OverheadsExactTypeGuards",
)


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise SystemExit(f"OVERHEADS_PUBLICATION_REJECTED: {reason}")


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def cmd(*args: str) -> str:
    return subprocess.check_output(args, cwd=PROJECT, text=True).strip()


def main() -> None:
    selection = load(PIPE / "model_processor_overheads_selection.json")
    baseline = load(PIPE / "model_processor_restricted_supply_module_status.json")
    require(selection["source_file"] == SOURCE_FILE
            and selection["source_commit"] == SOURCE_COMMIT
            and selection["rank"] == 50 and selection["layer"] == 10
            and selection["file_dag_ready"]
            and selection["direct_internal_dependencies"] == ["behavior/all.v"]
            and selection["targets_in_source_order"] == list(NAMES),
            "selection/DAG/order mismatch")
    require(baseline["status"] == "PASS"
            and baseline["coverage"]["accepted_files"] == 50
            and baseline["coverage"]["accepted_declarations"] == 364,
            "published baseline changed")

    pinned = VALIDATION / ".work/prosa-v06-414e667"
    official = pinned / SOURCE_FILE
    source_copy = WORK / "source" / SOURCE_FILE
    require(cmd("git", "-C", str(pinned), "rev-parse", "HEAD") == SOURCE_COMMIT
            and cmd("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}")
            == "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
            and not cmd("git", "-C", str(pinned), "status", "--porcelain",
                        "--untracked-files=all"),
            "official source checkout not pinned/clean")
    old1 = "  Next Obligation. by move => j [] // s [] /=; case: eqP. Qed."
    old2 = ("  Next Obligation. by move => j [] // s [] //=; "
            "rewrite [s == j]eq_sym; case (j == s). Qed.")
    new1 = "  Next Obligation. by case: s => [|a b|a|a|a] //=; case: eqP. Qed."
    new2 = ("  Next Obligation.\n"
            "    move: H; case: s => [|a b|a|a|a] //=.\n"
            "    by rewrite [a == j]eq_sym; case: (j == a).\n"
            "  Qed.")
    original = official.read_text()
    require(original.count(old1) == original.count(old2) == 1
            and source_copy.read_text() == original.replace(old1, new1).replace(old2, new2),
            "Rocq 9.3 compatibility copy modified source declaration content")
    patch = VALIDATION / "patches/prosa-v06-rocq93-model-processor-overheads.patch"
    source_vo = source_copy.with_suffix(".vo")
    require(sha(patch) and sha(source_vo)
            and source_vo.stat().st_mtime_ns > source_copy.stat().st_mtime_ns,
            "source compatibility build stale")
    source_type_log = WORK / "source_audit.log"
    source_types = source_type_log.read_text()
    require("Error:" not in source_types and all(n in source_types for n in NAMES),
            "source elaborated type audit incomplete")
    with (VALIDATION / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE_FILE]
    require([r["declaration_name"] for r in rows] == list(NAMES),
            "public source inventory changed")
    type_evidence = load(VALIDATION / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
                f"source elaborated type fingerprint changed: {row['declaration_name']}")

    dep = load(PIPE / "behavior_all_module_manifest.json")
    dep_status = load(PIPE / "behavior_all_module_status.json")
    require(dep["acceptance"] == "ACCEPTED_V06_FILE"
            and dep_status["status"] == "PASS"
            and sha(PROJECT / dep["production_file"]) == dep["production_source_sha256"],
            "file-DAG dependency no longer accepted/current")
    olean_dir = WORK / "olean"
    require(sha(olean_dir / "Prosa/Behavior/All.olean")
            == dep["production_olean_sha256"],
            "accepted dependency .olean changed")
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

    production = PROJECT / "Prosa/Model/Processor/Overheads.lean"
    target_olean = olean_dir / "Prosa/Model/Processor/Overheads.olean"
    guard_source = VALIDATION / "fixtures/translation_order/OverheadsComputationInterface.lean"
    guard_olean = olean_dir / "Validation/fixtures/translation_order/OverheadsComputationInterface.olean"
    require(sha(production) and sha(target_olean) and sha(guard_source)
            and sha(guard_olean)
            and target_olean.stat().st_mtime_ns > production.stat().st_mtime_ns
            and guard_olean.stat().st_mtime_ns > target_olean.stat().st_mtime_ns
            and guard_olean.stat().st_mtime_ns > guard_source.stat().st_mtime_ns
            and guard_source.read_text().count(" := rfl") == 3,
            "production/three Lean-kernel projection guards stale")
    require(not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text()),
            "forbidden Lean escape")
    lean_audit = WORK / "lean_audit_rewritten.log"
    audit_text = lean_audit.read_text()
    require("error:" not in audit_text and "sorryAx" not in audit_text
            and all(f"{LEAN_MODULE}.{n}" in audit_text for n in NAMES[1:])
            and all(f"'{LEAN_MODULE}.{n}' does not depend on any axioms"
                    in audit_text for n in NAMES[1:4])
            and "[propext, Classical.choice, Quot.sound]" in audit_text,
            "Lean #print axioms audit changed")

    config_path = VALIDATION / "tooling/model_processor_overheads_full_dependency_export_config.json"
    config = load(config_path)
    export = WORK / "OverheadsFullRewritten.out"
    metadata_path = WORK / "export_full_rewritten_metadata.json"
    metadata = load(metadata_path)
    imported = WORK / "imported_full_rewritten"
    import_source = imported / "ImportedOverheads.v"
    import_vo = imported / "ImportedOverheads.vo"
    require(config["targets"][:len(NAMES)] == [f"{LEAN_MODULE}.{n}" for n in NAMES]
            and len(config["targets"]) == len(NAMES) + 3
            and config["statement_only"] == [] and config["body_theorems"] == []
            and len(config["normalization"]["body_projections"]) == 3
            and metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 0
            and metadata["kernel_guard_artifacts"][str(guard_source)] == sha(guard_source)
            and sha(imported / export.name) == sha(export)
            and import_source.read_text() ==
              'From LeanImport Require Import Lean.\nLean Import "OverheadsFullRewritten.out".\n'
            and sha(import_vo) and import_vo.stat().st_mtime_ns > export.stat().st_mtime_ns,
            "actual compiled export/import/guard binding changed")
    budget_path = WORK / "dependency_budget_full_rewritten.json"
    budget = load(budget_path)
    require(budget["export_sha256"] == sha(export)
            and budget["explicit_export_root_count"] == len(NAMES) + 3
            and set(budget["statement_only_serialized_names"])
            == {"propext", "Classical.choice", "Quot.sound"},
            "dependency budget has new statement-only frontier")

    cert_root = VALIDATION / "certificates/model_processor"
    for name in MODULES:
        v, vo = cert_root / f"{name}.v", cert_root / f"{name}.vo"
        require(sha(v) and sha(vo) and vo.stat().st_mtime_ns > v.stat().st_mtime_ns,
                f"certificate missing/stale: {name}")
        require(not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", v.read_text()),
                f"forbidden certificate escape: {name}")
    guards = cert_root / "OverheadsExactTypeGuards.v"
    require(all(f"Check (@prosa.model.processor.overheads.{n}" in guards.read_text()
                and f"Check (ImportedOverheads.Prosa_Model_Processor_Overheads_{n}" in guards.read_text()
                for n in NAMES), "exact-type guard incomplete")
    guard_log = WORK / "exact_type_guards_full.log"
    require("Error:" not in guard_log.read_text()
            and all(n in guard_log.read_text() for n in NAMES),
            "exact-type guard compile log incomplete")
    adapter_meta_path = WORK / "base_adapter_full_metadata.json"
    adapter_meta = load(adapter_meta_path)
    require(adapter_meta["imported_artifact_sha256"] == sha(export)
            and adapter_meta["output_sha256"] == sha(cert_root / "OverheadsBaseAdapter.v")
            and adapter_meta["semantic_assumptions_added"] == [],
            "generated adapter not bound to current artifact")
    audit_v = VALIDATION / "fixtures/translation_order/OverheadsAssumptionAudit.v"
    audit_vo = audit_v.with_suffix(".vo")
    audit_log = WORK / "assumption_audit_full.log"
    summary_path = WORK / "assumption_summary_full.json"
    summary = load(summary_path)
    require(sha(audit_v) and sha(audit_vo) and sha(audit_log)
            and audit_vo.stat().st_mtime_ns > (cert_root / "OverheadsCorrespondence.vo").stat().st_mtime_ns
            and summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(NAMES),
            "marked assumption audit missing/stale")
    for name, cert in zip(NAMES, CERTIFICATES, strict=True):
        item = summary["certificates"][name]
        expected = ("CERTIFIED_WITH_PROP_SPROP_FOUNDATION" if name in PROP_TARGETS
                    else "CERTIFIED")
        require(item["certificate"] == cert and item["status"] == expected
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"],
                f"semantic assumption gate failed: {name}")
    require(not cmd("git", "-C", str(PROJECT.parent), "status", "--porcelain",
                    "--", "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(PROJECT.parent), "diff", "--check"], check=True)

    output = VALIDATION / "imported/translation_order/overheads"
    require(not output.exists(), "publication directory already exists")
    output.parent.mkdir(parents=True, exist_ok=True)
    staged = Path(tempfile.mkdtemp(prefix=".overheads.", dir=output.parent))
    for src in (export, metadata_path, budget_path, import_source, import_vo,
                audit_log, summary_path, guard_log, lean_audit, source_type_log,
                adapter_meta_path):
        shutil.copy2(src, staged / src.name)
    (staged / "certificates").mkdir()
    for name in MODULES:
        for ext in (".v", ".vo"):
            src = cert_root / f"{name}{ext}"
            shutil.copy2(src, staged / "certificates" / src.name)
    require(sha(staged / export.name) == sha(export)
            and sha(staged / import_vo.name) == sha(import_vo),
            "staged artifact corrupted")
    staged.rename(output)

    artifacts = {
        "official_source": official,
        "compatibility_patch": patch,
        "validation_source": source_copy,
        "source_vo": source_vo,
        "source_type_log": output / source_type_log.name,
        "production_source": production,
        "production_olean": target_olean,
        "kernel_guard_source": guard_source,
        "kernel_guard_olean": guard_olean,
        "lean_audit": output / lean_audit.name,
        "export_config": config_path,
        "export": output / export.name,
        "imported_v": output / import_source.name,
        "imported_vo": output / import_vo.name,
        "adapter_metadata": output / adapter_meta_path.name,
        "certificate_v": cert_root / "OverheadsCorrespondence.v",
        "certificate_vo": output / "certificates/OverheadsCorrespondence.vo",
        "exact_type_guard_v": guards,
        "exact_type_guard_vo": output / "certificates/OverheadsExactTypeGuards.vo",
        "assumption_log": output / audit_log.name,
        "assumption_summary": output / summary_path.name,
        "dependency_budget": output / budget_path.name,
    }
    declarations = []
    for row, cert in zip(rows, CERTIFICATES, strict=True):
        name = row["declaration_name"]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
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
        "rank": 50,
        "acceptance": "ACCEPTED_V06_FILE",
        "build_mode": "FILE_VALIDATE",
        "dependency_reuse": "VERIFIED_ACCEPTED_BEHAVIOR_ALL_OLEAN",
        "target_build": "FRESH_CURRENT_SNAPSHOT",
        "source_acquisition": "PINNED_SOURCE_WITH_PROOF_SCRIPT_ONLY_ROCQ93_PATCH",
        "translation_file": str(production.relative_to(PROJECT)),
        "proof_clean": True,
        "actual_compiled_artifact_imported": True,
        "declarations": declarations,
        "artifact_hashes": {key: sha(value) for key, value in artifacts.items()},
        "artifact_paths": {key: str(value.relative_to(PROJECT))
                           for key, value in artifacts.items()},
        "accepted_dependency_manifest_sha256": {
            "behavior_all": sha(PIPE / "behavior_all_module_manifest.json")
        },
        "tooling_manifest_sha256": sha(VALIDATION / "tooling/tooling_manifest.json"),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_file = PIPE / "model_processor_overheads_module_manifest.json"
    manifest_file.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = dict(baseline["coverage"])
    coverage["accepted_files"] += 1
    coverage["accepted_declarations"] += len(NAMES)
    status = {
        "slice": "MODEL_PROCESSOR_OVERHEADS",
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
    status_file = PIPE / "model_processor_overheads_module_status.json"
    status_file.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "accepted_files": coverage["accepted_files"],
                      "accepted_declarations": coverage["accepted_declarations"],
                      "published": str(output)}, sort_keys=True))


if __name__ == "__main__":
    main()
