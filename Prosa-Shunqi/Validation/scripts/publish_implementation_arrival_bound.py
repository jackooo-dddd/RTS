#!/usr/bin/env python3
"""Fail-closed whole-file publication for pinned arrival_bound.v."""

from __future__ import annotations

import csv
import hashlib
import json
import subprocess
from datetime import datetime
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
WORK = PROJECT / "Validation/.work/experiments/implementation_arrival_bound"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
SOURCE = PROJECT / "Validation/.work/prosa-v06-414e667"
SOURCE_FILE = "implementation/definitions/arrival_bound.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TARGETS = ["task_arrivals_bound", "task_arrivals_bound_eqdef", "eqn_task_arrivals_bound"]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty artifact: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    sha(path)
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read_json(PIPELINE / "implementation_arrival_bound_selection.json")
    require(selection["rank"] == 35 and selection["file_dag_ready"]
            and selection["targets_in_source_order"] == TARGETS,
            "rank/file DAG/target selection mismatch")
    require(command("git", "-C", str(SOURCE), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(SOURCE), "status", "--porcelain"),
            "official source checkout not clean pinned v0.6")
    source_sha = sha(SOURCE / SOURCE_FILE)
    require(source_sha == selection["source_sha256"], "official source changed")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as file:
        rows = [row for row in csv.DictReader(file) if row["source_file"] == SOURCE_FILE]
    require([row["declaration_name"] for row in rows] == TARGETS,
            "whole-file declaration inventory mismatch")

    previous_path = PIPELINE / "analysis_sbf_sbf_module_status.json"
    previous = read_json(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 33
            and previous["coverage"]["accepted_declarations"] == 303,
            "published baseline changed")
    dependency_manifest = PIPELINE / "implementation_extrapolated_arrival_curve_module_manifest.json"
    dependency_status = read_json(PIPELINE / "implementation_extrapolated_arrival_curve_module_status.json")
    require(dependency_status["per_file"]["implementation/definitions/extrapolated_arrival_curve.v"]["status"]
            == "ACCEPTED_V06_FILE", "file DAG dependency not accepted")
    dependency = read_json(dependency_manifest)
    require(sha(PROJECT / "Prosa/Implementation/Definitions/ExtrapolatedArrivalCurve.lean")
            == dependency["artifact_hashes"]["production_source_sha256"],
            "Rank 33 accepted dependency changed")

    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version"),
            "Lean version changed")
    require(command("git", "-C", str(PROJECT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474",
            "Mathlib revision changed")
    rocq_version = command("opam", "exec", "--switch=rocq93rc1", "--", "rocq", "--version")
    require("9.3" in rocq_version, "Rocq importer environment changed")

    source_meta = read_json(WORK / "source_metadata.json")
    replay_meta = read_json(WORK / "source_metadata_regenerated.json")
    require(source_meta["source_commit"] == PIN and source_meta["source_file_sha256"] == source_sha
            and source_meta["declarations"] == replay_meta["declarations"]
            and sha(WORK / "source/OfficialArrivalBound.v")
            == sha(WORK / "source/OfficialArrivalBoundRegenerated.v"),
            "official source extraction replay failed")
    for row in rows[:2]:
        block = source_meta["declarations"][row["declaration_name"]]
        require(block["acquisition_mode"] == "BODY_EXACT"
                and block["source_block_sha256"] == block["generated_text_sha256"]
                == row["source_command_sha256"],
                f"source computational declaration changed: {row['declaration_name']}")
    lemma = source_meta["declarations"]["eqn_task_arrivals_bound"]
    require(lemma["acquisition_mode"] == "STATEMENT_EXACT_PROOF_OMITTED"
            and lemma["statement_sort"] == "Type"
            and lemma["elaborated_type_evidence"] == "ELABORATED_ROCQ_CHECK"
            and lemma["source_statement_sha256"] == lemma["normalized_statement_sha256"],
            "informative source theorem statement fidelity failed")

    lean_log = (WORK / "lean_preflight.log").read_text()
    require("eqn_task_arrivals_bound :" in lean_log
            and "task_arrivals_bound_eqdef :" in lean_log
            and "does not depend on any axioms" in lean_log
            and "depends on axioms: [propext]" in lean_log
            and "sorryAx" not in lean_log and "error:" not in lean_log,
            "Lean proof-clean or complete-type audit failed")
    for path in [PROJECT / "Prosa/Implementation/Definitions/ArrivalBound.lean",
                 PROJECT / "Validation/certificates/implementation/ArrivalBoundArtifactAdapter.v",
                 PROJECT / "Validation/certificates/implementation/ArrivalBoundCorrespondence.v"]:
        text = path.read_text()
        require(not any(bad in text for bad in ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden placeholder/axiom: {path}")

    module_olean = WORK / "olean/Prosa/Implementation/Definitions/ArrivalBound.olean"
    require(sha(module_olean)
            == sha(PROJECT / ".lake/build/lib/lean/Prosa/Implementation/Definitions/ArrivalBound.olean"),
            "exporter module olean differs from isolated fresh build")
    config_path = PROJECT / "Validation/tooling/implementation_arrival_bound_export_config.json"
    config = read_json(config_path)
    export_meta = read_json(WORK / "export_metadata.json")
    require(config["module"] == "Prosa.Implementation.Definitions.ArrivalBound"
            and len(config["targets"]) == 6 and not config["statement_only"]
            and not config["body_theorems"]
            and export_meta["config_sha256"] == sha(config_path)
            and export_meta["output_sha256"] == sha(WORK / "ArrivalBound.out"),
            "actual Lean export/config mismatch")
    require('Lean Import "Validation/.work/experiments/implementation_arrival_bound/ArrivalBound.out".'
            in (WORK / "ImportedArrivalBound.v").read_text(),
            "imported Rocq module points to wrong export")

    audit = read_json(WORK / "assumption_summary.json")
    expected_audits = {
        "task_arrivals_bound_source_roundtrip", "task_arrivals_bound_target_roundtrip",
        "task_arrivals_bound_periodic", "task_arrivals_bound_sporadic",
        "task_arrivals_bound_prefix", "task_arrivals_bound_eqdef",
        "eqn_task_arrivals_bound",
    }
    require(audit["audit_policy"] == "fail_closed"
            and set(audit["certificates"]) == expected_audits,
            "incomplete fail-closed certificate audit")
    for name, record in audit["certificates"].items():
        expected_status = ("CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                           if name in {"task_arrivals_bound_eqdef", "eqn_task_arrivals_bound"}
                           else "CERTIFIED")
        require(record["status"] == expected_status
                and not record["semantic_premises"]
                and not record["statement_only_dependencies"]
                and not record["source_theorem_dependency"]
                and not record["target_theorem_dependency"]
                and not record["unexpected"], f"certificate audit failed: {name}")
    require(not command("git", "-C", str(PROJECT.parent), "diff", "--check"),
            "git diff --check failed")

    artifacts = {
        "source_signature": WORK / "source/OfficialArrivalBound.v",
        "source_signature_vo": WORK / "source/OfficialArrivalBound.vo",
        "source_metadata": WORK / "source_metadata.json",
        "source_replay_metadata": WORK / "source_metadata_regenerated.json",
        "production_source": PROJECT / "Prosa/Implementation/Definitions/ArrivalBound.lean",
        "production_olean": module_olean,
        "dependency_manifest": dependency_manifest,
        "export_config": config_path,
        "export": WORK / "ArrivalBound.out",
        "imported_source": WORK / "ImportedArrivalBound.v",
        "imported_vo": WORK / "ImportedArrivalBound.vo",
        "adapter_source": PROJECT / "Validation/certificates/implementation/ArrivalBoundArtifactAdapter.v",
        "adapter_vo": PROJECT / "Validation/certificates/implementation/ArrivalBoundArtifactAdapter.vo",
        "certificate_source": PROJECT / "Validation/certificates/implementation/ArrivalBoundCorrespondence.v",
        "certificate_vo": PROJECT / "Validation/certificates/implementation/ArrivalBoundCorrespondence.vo",
        "assumption_audit_source": PROJECT / "Validation/certificates/implementation/ArrivalBoundAssumptionAudit.v",
        "assumption_audit_vo": PROJECT / "Validation/certificates/implementation/ArrivalBoundAssumptionAudit.vo",
        "assumption_config": PROJECT / "Validation/certificates/implementation/arrival_bound_assumption_config.json",
        "assumption_summary": WORK / "assumption_summary.json",
        "lean_preflight": WORK / "lean_preflight.log",
    }
    hashes = {name + "_sha256": sha(path) for name, path in artifacts.items()}
    snapshot = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    target_prefix = "Prosa.Implementation.Definitions.ArrivalBound."
    records = []
    for row in rows:
        name = row["declaration_name"]
        audits = ([audit["certificates"][key] for key in sorted(expected_audits)
                   if key.startswith("task_arrivals_bound_") and key != "task_arrivals_bound_eqdef"]
                  if name == "task_arrivals_bound" else
                  [audit["certificates"]["task_arrivals_bound_eqdef"]]
                  if name == "task_arrivals_bound_eqdef" else
                  [audit["certificates"]["eqn_task_arrivals_bound"]])
        records.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": target_prefix + name,
            "source_kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_fingerprint": row["final_type_or_type_fingerprint"],
            "semantic_status": ("CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                                if name != "task_arrivals_bound" else "CERTIFIED"),
            "certificate_bundle": [item["certificate"] for item in audits],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": (["PropSPropFoundation.interpret_strict"]
                                      if name != "task_arrivals_bound" else []),
            "unexpected_assumptions": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": "TRANSLATION_ORDER_IMPLEMENTATION_ARRIVAL_BOUND",
        "generated_at": datetime.now().astimezone().isoformat(),
        "source_file": SOURCE_FILE, "source_commit": PIN,
        "source_file_sha256": source_sha,
        "production_file": "Prosa/Implementation/Definitions/ArrivalBound.lean",
        "lean_version": "4.33.1", "mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
        "rocq_version": rocq_version,
        "representation": "three-constructor inductive with two-sided prefix/Nat payload relation and informative reflection",
        "snapshot_id": snapshot, "artifact_hashes": hashes,
        "declarations": records, "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = PIPELINE / "implementation_arrival_bound_module_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": "TRANSLATION_ORDER_IMPLEMENTATION_ARRIVAL_BOUND",
        "per_file": {SOURCE_FILE: {
            "public_declarations": 3, "translated": 3, "proof_clean": 3,
            "certified": 3, "certified_without_prop_sprop_foundation": 1,
            "certified_with_prop_sprop_foundation": 2,
            "status": "ACCEPTED_V06_FILE"}},
        "coverage": {"accepted_files": 34, "authoritative_files": 357,
                     "accepted_declarations": 306, "authoritative_declarations": 2439,
                     "translated_but_not_certified": 0, "deferred_external_boundary": 239},
        "previous_status_sha256": sha(previous_path),
        "manifest_sha256": sha(manifest_path),
        "snapshot_id": snapshot, "status": "PASS",
    }
    (PIPELINE / "implementation_arrival_bound_module_status.json").write_text(
        json.dumps(status, indent=2) + "\n")
    print("PUBLISHED implementation/definitions/arrival_bound.v: 3/3; cumulative 306/2439, 34/357")


if __name__ == "__main__":
    main()
