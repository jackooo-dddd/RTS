#!/usr/bin/env python3
"""Fail-closed publication for the one-class official SBF module."""

from __future__ import annotations

import csv
import hashlib
import json
import subprocess
from datetime import datetime
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
WORK = PROJECT / "Validation/.work/experiments/analysis_sbf_sbf"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
SOURCE = PROJECT / "Validation/.work/prosa-v06-414e667"
SOURCE_FILE = "analysis/definitions/sbf/sbf.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing artifact: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = load(PIPELINE / "analysis_sbf_sbf_selection.json")
    require(selection["rank"] == 34 and selection["file_dag_ready"]
            and selection["targets_in_source_order"] == ["SupplyBoundFunction"],
            "file DAG/selection mismatch")
    require(command("git", "-C", str(SOURCE), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(SOURCE), "status", "--porcelain"),
            "official source checkout is not clean pinned v0.6")
    source_sha = sha(SOURCE / SOURCE_FILE)
    require(source_sha == selection["source_sha256"], "official source file changed")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as file:
        rows = [r for r in csv.DictReader(file) if r["source_file"] == SOURCE_FILE]
    require(len(rows) == 1 and rows[0]["declaration_name"] == "SupplyBoundFunction"
            and rows[0]["kind"] == "Class", "source inventory mismatch")
    meta = load(WORK / "source_metadata.json")
    replay = load(WORK / "source_metadata_regenerated.json")
    block = meta["declarations"]["SupplyBoundFunction"]
    require(meta["source_commit"] == PIN and meta["source_file_sha256"] == source_sha
            and meta["declarations"] == replay["declarations"]
            and sha(WORK / "source/OfficialSbf.v") == sha(WORK / "source/OfficialSbfRegenerated.v")
            and block["acquisition_mode"] == "BODY_EXACT"
            and block["source_block_sha256"] == block["generated_text_sha256"]
            and block["source_block_sha256"] == rows[0]["source_command_sha256"],
            "official class extraction fidelity failed")

    previous_path = PIPELINE / "implementation_extrapolated_arrival_curve_module_status.json"
    previous = load(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 32
            and previous["coverage"]["accepted_declarations"] == 302,
            "published baseline changed")
    job_status = load(PIPELINE / "behavior_job_module_status.json")
    job_manifest = load(PIPELINE / "behavior_job_module_manifest.json")
    require(job_status["per_file"]["behavior/job.v"]["status"] == "ACCEPTED_V06_FILE",
            "SBF file DAG dependency not accepted")
    reuse = load(WORK / "reuse_job_evidence.json")
    require(reuse["status"] == "PASS" and reuse["mode"] == "VERIFIED_CACHE"
            and reuse["producer_accepted_manifest_sha256"] == sha(
                PIPELINE / "behavior_service_module_manifest.json")
            and reuse["modules"]["Prosa/Behavior/Job.olean"] == job_manifest["production_olean_sha256"]
            and sha(WORK / "olean/Prosa/Behavior/Job.olean") == job_manifest["production_olean_sha256"],
            "accepted Job dependency artifact not verified")
    for relative, expected in reuse["modules"].items():
        require(sha(WORK / "olean" / relative) == expected,
                f"dependency cache corrupted: {relative}")

    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version"),
            "Lean version changed")
    require(command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474",
            "Mathlib commit changed")
    rocq_version = command("opam", "exec", "--switch=rocq93rc1", "--", "rocq", "--version")
    require("9.3" in rocq_version, "Rocq importer environment changed")
    lean_log = (WORK / "lean_preflight.log").read_text()
    require("SupplyBoundFunction.mk" in lean_log
            and "SupplyBoundFunction.supply_bound_function" in lean_log
            and "'Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction' does not depend on any axioms" in lean_log
            and "sorryAx" not in lean_log and "error:" not in lean_log,
            "Lean proof/type preflight failed")

    config_path = PROJECT / "Validation/tooling/analysis_sbf_sbf_export_config.json"
    config = load(config_path)
    export_meta = load(WORK / "export_metadata.json")
    require(config["module"] == "Prosa.Analysis.Definitions.Sbf.Sbf"
            and len(config["targets"]) == 3 and not config["statement_only"]
            and not config["body_theorems"]
            and export_meta["config_sha256"] == sha(config_path)
            and export_meta["output_sha256"] == sha(WORK / "Sbf.out"),
            "actual class/constructor/projection export mismatch")
    require('Lean Import "Validation/.work/experiments/analysis_sbf_sbf/Sbf.out".'
            in (WORK / "ImportedSbf.v").read_text(),
            "imported Rocq module points to another artifact")

    audit = load(WORK / "assumption_summary.json")
    require(audit["audit_policy"] == "fail_closed" and
            set(audit["certificates"]) == {
                "export_field", "import_field", "source_roundtrip", "target_roundtrip"},
            "class certificate audit incomplete")
    for name, record in audit["certificates"].items():
        require(record["status"] == "CERTIFIED"
                and not record["prop_sprop_foundation"]
                and not record["semantic_premises"]
                and not record["statement_only_dependencies"]
                and not record["source_theorem_dependency"]
                and not record["target_theorem_dependency"]
                and not record["unexpected"],
                f"class audit failed: {name}")
    require(not command("git", "-C", str(PROJECT.parent), "diff", "--check"),
            "git diff --check failed")

    artifacts = {
        "source_signature": WORK / "source/OfficialSbf.v",
        "source_signature_vo": WORK / "source/OfficialSbf.vo",
        "source_metadata": WORK / "source_metadata.json",
        "production_source": PROJECT / "Prosa/Analysis/Definitions/Sbf/Sbf.lean",
        "production_olean": WORK / "olean/Prosa/Analysis/Definitions/Sbf/Sbf.olean",
        "dependency_reuse_evidence": WORK / "reuse_job_evidence.json",
        "export_config": config_path,
        "export": WORK / "Sbf.out",
        "imported_source": WORK / "ImportedSbf.v",
        "imported_vo": WORK / "ImportedSbf.vo",
        "certificate_source": PROJECT / "Validation/certificates/analysis/SbfCorrespondence.v",
        "certificate_vo": PROJECT / "Validation/certificates/analysis/SbfCorrespondence.vo",
        "assumption_audit_source": PROJECT / "Validation/certificates/analysis/SbfAssumptionAudit.v",
        "assumption_audit_vo": PROJECT / "Validation/certificates/analysis/SbfAssumptionAudit.vo",
        "assumption_config": PROJECT / "Validation/certificates/analysis/sbf_assumption_config.json",
        "assumption_summary": WORK / "assumption_summary.json",
        "lean_preflight": WORK / "lean_preflight.log",
    }
    hashes = {name + "_sha256": sha(path) for name, path in artifacts.items()}
    snapshot = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    manifest = {
        "slice": "TRANSLATION_ORDER_ANALYSIS_SBF_SBF",
        "generated_at": datetime.now().astimezone().isoformat(),
        "source_file": SOURCE_FILE,
        "source_commit": PIN,
        "source_file_sha256": source_sha,
        "source_command_sha256": rows[0]["source_command_sha256"],
        "source_elaborated_type_fingerprint": rows[0]["final_type_or_type_fingerprint"],
        "production_file": "Prosa/Analysis/Definitions/Sbf/Sbf.lean",
        "lean_version": "4.33.1",
        "mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
        "rocq_version": rocq_version,
        "representation": "source function type ↔ imported Lean single-field record; two-sided pointwise roundtrip",
        "dependency_reuse": "VERIFIED_CACHE from accepted Service producer, including Job closure",
        "snapshot_id": snapshot,
        "artifact_hashes": hashes,
        "declarations": [{
            "source_declaration": rows[0]["qualified_name"],
            "lean_declaration": "Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction",
            "kind": "Class",
            "semantic_status": "CERTIFIED",
            "certificate_bundle": [r["certificate"] for r in audit["certificates"].values()],
            "semantic_premises": [],
            "statement_only_dependencies": [],
            "prop_sprop_foundation": [],
            "unexpected_assumptions": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        }],
        "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = PIPELINE / "analysis_sbf_sbf_module_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": "TRANSLATION_ORDER_ANALYSIS_SBF_SBF",
        "per_file": {SOURCE_FILE: {
            "public_declarations": 1, "translated": 1, "proof_clean": 1,
            "certified": 1, "certified_without_prop_sprop_foundation": 1,
            "certified_with_prop_sprop_foundation": 0,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": {
            "accepted_files": 33, "authoritative_files": 357,
            "accepted_declarations": 303, "authoritative_declarations": 2439,
            "translated_but_not_certified": 0,
            "deferred_external_boundary": 239,
        },
        "previous_status_sha256": sha(previous_path),
        "manifest_sha256": sha(manifest_path),
        "snapshot_id": snapshot,
        "status": "PASS",
    }
    (PIPELINE / "analysis_sbf_sbf_module_status.json").write_text(
        json.dumps(status, indent=2) + "\n")
    print("PUBLISHED analysis/definitions/sbf/sbf.v: 1/1 CERTIFIED; "
          "cumulative 303/2439, 33/357")


if __name__ == "__main__":
    main()
