#!/usr/bin/env python3
"""Fail-closed publication of the Rank 33 full-artifact correspondence run."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import subprocess
from datetime import datetime
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
WORK = PROJECT / "Validation/.work/experiments/extrapolated_full"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
SOURCE = PROJECT / "Validation/.work/prosa-v06-414e667"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE_FILE = "implementation/definitions/extrapolated_arrival_curve.v"
LEAN_MODULE = "Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve"
SLICE = "TRANSLATION_ORDER_IMPLEMENTATION_EXTRAPOLATED_ARRIVAL_CURVE"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def digest(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def run(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def audit_lean_log(path: Path, expected: set[str]) -> None:
    log = path.read_text()
    require("sorryAx" not in log and "error:" not in log,
            f"Lean proof audit contains forbidden text: {path}")
    allowed = {"propext", "Quot.sound"}
    for declaration in expected:
        pattern = rf"'{re.escape(declaration)}' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])"
        matches = re.findall(pattern, log, flags=re.MULTILINE)
        require(len(matches) == 1, f"Lean axiom record missing or duplicate: {declaration}")
        axioms = {x.strip() for x in matches[0].split(",") if x.strip()}
        require(axioms <= allowed,
                f"unexpected Lean axioms for {declaration}: {sorted(axioms - allowed)}")


def main() -> None:
    selection = read_json(PIPELINE / "implementation_extrapolated_arrival_curve_selection.json")
    names = selection["targets_in_source_order"]
    require(len(names) == 21 and len(set(names)) == 21, "target count/order changed")
    require(selection["rank"] == 33 and selection["file_dag_ready"] is True,
            "Rank 33 file DAG is not ready")

    source_commit = run("git", "-C", str(SOURCE), "rev-parse", "HEAD")
    require(source_commit == PIN, "pinned source commit changed")
    require(not run("git", "-C", str(SOURCE), "status", "--porcelain"),
            "pinned source checkout is dirty")
    source_sha = digest(SOURCE / SOURCE_FILE)
    require(source_sha == selection["source_sha256"], "authoritative source hash changed")

    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as file:
        inventory = [row for row in csv.DictReader(file)
                     if row["source_file"] == SOURCE_FILE]
    require([r["declaration_name"] for r in sorted(
        inventory, key=lambda r: int(r["source_order"]))] == names,
        "source inventory disagrees with 21 targets")
    inventory_by_name = {r["declaration_name"]: r for r in inventory}

    original = WORK / "source/OfficialExtrapolatedArrivalCurve.v"
    regenerated = WORK / "source/OfficialExtrapolatedArrivalCurveRegenerated.v"
    require(digest(original) == digest(regenerated),
            "official source extraction replay changed")
    source_meta = read_json(WORK / "source_metadata.json")
    source_meta_replay = read_json(WORK / "source_metadata_regenerated.json")
    require(source_meta["source_commit"] == PIN
            and source_meta["source_file_sha256"] == source_sha,
            "source acquisition provenance changed")
    require(source_meta["declarations"] == source_meta_replay["declarations"]
            and set(source_meta["declarations"]) == set(names),
            "source declaration extraction differs on replay")
    for name, record in source_meta["declarations"].items():
        if record["source_kind"] == "computational":
            require(record["acquisition_mode"] == "BODY_EXACT"
                    and record["source_block_sha256"] == record["generated_text_sha256"],
                    f"source body is not byte-identical: {name}")
        else:
            require(record["acquisition_mode"] == "STATEMENT_EXACT_PROOF_OMITTED"
                    and record["elaborated_type_evidence"] == "ELABORATED_ROCQ_CHECK",
                    f"source theorem type evidence missing: {name}")

    require("Lean (version 4.33.1" in run("lake", "env", "lean", "--version"),
            "Lean toolchain changed")
    mathlib = run("git", "-C", str(PROJECT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
    require(mathlib == "0df444a360eaa60ab8c11dca51a86af692955474",
            "Mathlib revision changed")
    rocq_version = run("opam", "exec", "--switch=rocq93rc1", "--", "rocq", "--version")
    require("9.3" in rocq_version, "Rocq 9.3 importer environment changed")

    audit_lean_log(WORK / "production_preflight_and_axioms.log", {
        f"{LEAN_MODULE}.large_horizon_iff",
        f"{LEAN_MODULE}.large_horizon_P",
        f"{LEAN_MODULE}.valid_arrival_curve_prefix_P",
    })
    interface_prefix = "Prosa.Validation.ExtrapolatedArrivalCurveArithmeticInterface."
    audit_lean_log(WORK / "arithmetic_interface_axioms.log", {
        interface_prefix + name for name in (
            "production_div_add_mod", "production_mod_lt",
            "production_div_zero", "production_mod_zero")
    })

    config = read_json(PROJECT / "Validation/tooling/implementation_extrapolated_arrival_curve_arithmetic_export_config.json")
    require(config["module"] == "Validation.fixtures.translation_order.ExtrapolatedArrivalCurveArithmeticInterface"
            and len(config["targets"]) == 25 and len(config["body_theorems"]) == 4
            and not config["statement_only"], "actual-artifact export boundary changed")
    require([x.rsplit(".", 1)[-1] for x in config["definition_targets"]] == names,
            "exported production declaration list differs from source inventory")
    metadata = read_json(WORK / "arithmetic_configured_export_metadata.json")
    export_sha = digest(WORK / "ExtrapolatedArrivalCurveArithmeticConfigured.out")
    require(metadata["config_sha256"] == digest(PROJECT / "Validation/tooling/implementation_extrapolated_arrival_curve_arithmetic_export_config.json")
            and metadata["output_sha256"] == export_sha
            and export_sha == digest(WORK / "ExtrapolatedArrivalCurveArithmetic.out")
            and metadata["statement_only_count"] == 0
            and metadata["body_theorem_count"] == 4,
            "configured export differs from imported artifact")
    imported_source = (WORK / "ImportedExtrapolatedArrivalCurve.v").read_text()
    require('Lean Import "ExtrapolatedArrivalCurveArithmetic.out".' in imported_source,
            "Rocq imported module points at another export")

    summary = read_json(WORK / "full_assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "assumption audit not fail-closed")
    records = summary["certificates"]
    expected = (set(names) - {"ArrivalCurvePrefix"}) | {
        "ArrivalCurvePrefix_source_roundtrip", "ArrivalCurvePrefix_target_roundtrip"}
    require(set(records) == expected, "assumption audit did not cover every declaration")
    for name, record in records.items():
        require(record["status"] in {"CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
                and not record["semantic_premises"]
                and not record["statement_only_dependencies"]
                and not record["source_theorem_dependency"]
                and not record["target_theorem_dependency"]
                and not record["unexpected"],
                f"semantic/assumption gate failed: {name}")
        require((record["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")
                == bool(record["prop_sprop_foundation"]),
                f"Prop/SProp status inconsistent: {name}")

    previous_path = PIPELINE / "util_superadditivity_module_status.json"
    previous = read_json(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 31
            and previous["coverage"]["accepted_declarations"] == 281,
            "formal baseline changed")
    require(not run("git", "-C", str(PROJECT.parent), "diff", "--check"),
            "git diff --check failed")

    paths = {
        "source_signature": original,
        "source_signature_vo": WORK / "source/OfficialExtrapolatedArrivalCurve.vo",
        "source_metadata": WORK / "source_metadata.json",
        "production_source": PROJECT / "Prosa/Implementation/Definitions/ExtrapolatedArrivalCurve.lean",
        "production_olean": PROJECT / ".lake/build/lib/lean/Prosa/Implementation/Definitions/ExtrapolatedArrivalCurve.olean",
        "arithmetic_interface_source": PROJECT / "Validation/fixtures/translation_order/ExtrapolatedArrivalCurveArithmeticInterface.lean",
        "arithmetic_interface_olean": WORK / "olean/Validation/fixtures/translation_order/ExtrapolatedArrivalCurveArithmeticInterface.olean",
        "export_config": PROJECT / "Validation/tooling/implementation_extrapolated_arrival_curve_arithmetic_export_config.json",
        "export": WORK / "ExtrapolatedArrivalCurveArithmetic.out",
        "imported_source": WORK / "ImportedExtrapolatedArrivalCurve.v",
        "imported_vo": WORK / "ImportedExtrapolatedArrivalCurve.vo",
        "certificate_source": PROJECT / "Validation/certificates/implementation/ExtrapolatedArrivalCurveFullCorrespondence.v",
        "certificate_vo": PROJECT / "Validation/certificates/implementation/ExtrapolatedArrivalCurveFullCorrespondence.vo",
        "assumption_audit_source": PROJECT / "Validation/certificates/implementation/ExtrapolatedArrivalCurveFullAssumptionAudit.v",
        "assumption_audit_vo": PROJECT / "Validation/certificates/implementation/ExtrapolatedArrivalCurveFullAssumptionAudit.vo",
        "assumption_config": PROJECT / "Validation/certificates/implementation/extrapolated_arrival_curve_full_assumption_config.json",
        "assumption_summary": WORK / "full_assumption_summary.json",
        "lean_proof_audit": WORK / "production_preflight_and_axioms.log",
        "lean_interface_audit": WORK / "arithmetic_interface_axioms.log",
    }
    hashes = {name + "_sha256": digest(path) for name, path in paths.items()}
    snapshot_id = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    entries = []
    for name in names:
        record = records["ArrivalCurvePrefix_target_roundtrip" if name == "ArrivalCurvePrefix" else name]
        source_record = source_meta["declarations"][name]
        entries.append({
            "source_declaration": inventory_by_name[name]["qualified_name"],
            "lean_declaration": LEAN_MODULE + "." + name,
            "kind": inventory_by_name[name]["kind"],
            "source_command_sha256": inventory_by_name[name]["source_command_sha256"],
            "source_block_sha256": source_record["source_block_sha256"],
            "source_elaborated_type_sha256": source_record["elaborated_type_sha256"],
            "semantic_status": record["status"],
            "certificate": record["certificate"],
            "semantic_premises": [],
            "statement_only_dependencies": [],
            "prop_sprop_foundation": record["prop_sprop_foundation"],
            "unexpected_assumptions": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": SLICE,
        "generated_at": datetime.now().astimezone().isoformat(),
        "source_file": SOURCE_FILE,
        "source_commit": PIN,
        "source_file_sha256": source_sha,
        "production_file": "Prosa/Implementation/Definitions/ExtrapolatedArrivalCurve.lean",
        "lean_version": "4.33.1",
        "mathlib_commit": mathlib,
        "rocq_version": rocq_version,
        "source_acquisition": "exact computational blocks; elaborated theorem statements; replay byte-identical",
        "export_mode": "25 exact targets, 21 production bodies plus 4 validation-only theorem proof bodies; zero statement-only",
        "snapshot_id": snapshot_id,
        "artifact_hashes": hashes,
        "declarations": entries,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    plain = sum(e["semantic_status"] == "CERTIFIED" for e in entries)
    status = {
        "slice": SLICE,
        "per_file": {SOURCE_FILE: {
            "public_declarations": 21,
            "translated": 21,
            "proof_clean": 21,
            "certified": 21,
            "certified_without_prop_sprop_foundation": plain,
            "certified_with_prop_sprop_foundation": 21 - plain,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": {
            "accepted_files": 32,
            "authoritative_files": 357,
            "accepted_declarations": 302,
            "authoritative_declarations": 2439,
            "translated_but_not_certified": 0,
            "deferred_external_boundary": 239,
        },
        "previous_status_sha256": digest(previous_path),
        "manifest_sha256": None,
        "snapshot_id": snapshot_id,
        "status": "PASS",
    }
    manifest_path = PIPELINE / "implementation_extrapolated_arrival_curve_module_manifest.json"
    status_path = PIPELINE / "implementation_extrapolated_arrival_curve_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status["manifest_sha256"] = digest(manifest_path)
    status_path.write_text(json.dumps(status, indent=2) + "\n")
    print(f"PUBLISHED {SOURCE_FILE}: 21/21, {plain} CERTIFIED, "
          f"{21 - plain} WITH_PROP_SPROP; cumulative 302/2439, 32/357")


if __name__ == "__main__":
    main()
