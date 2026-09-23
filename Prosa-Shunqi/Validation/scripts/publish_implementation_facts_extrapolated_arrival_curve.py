#!/usr/bin/env python3
"""Fail-closed, content-addressed publication of pinned Rank 36 facts."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import subprocess
from datetime import datetime
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
WORK = PROJECT / "Validation/.work/experiments/implementation_facts_extrapolated_arrival_curve"
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
SOURCE = PROJECT / "Validation/.work/prosa-v06-414e667"
SOURCE_FILE = "implementation/facts/extrapolated_arrival_curve.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
MODULE = "Prosa.Implementation.Facts.ExtrapolatedArrivalCurve"
IMPORTED = "ImportedExtrapolatedArrivalCurveFactsCombined"


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty artifact: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path: Path) -> dict:
    sha(path)
    return json.loads(path.read_text())


def cmd(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read_json(PIPELINE / "implementation_facts_extrapolated_arrival_curve_selection.json")
    targets = selection["targets_in_source_order"]
    require(selection["rank"] == 36 and selection["file_dag_ready"]
            and len(targets) == 10 and selection["source_file"] == SOURCE_FILE,
            "rank/selection/file-DAG readiness mismatch")
    require(cmd("git", "-C", str(SOURCE), "rev-parse", "HEAD") == PIN
            and not cmd("git", "-C", str(SOURCE), "status", "--porcelain"),
            "official source not clean pinned v0.6")
    source_sha = sha(SOURCE / SOURCE_FILE)
    require(source_sha == selection["source_sha256"], "official source file changed")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream) if row["source_file"] == SOURCE_FILE]
    require([row["declaration_name"] for row in rows] == targets,
            "public declaration inventory/order mismatch")

    previous_path = PIPELINE / "implementation_arrival_bound_module_status.json"
    previous = read_json(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 34
            and previous["coverage"]["accepted_declarations"] == 306,
            "published previous Rank 35 baseline changed")
    dep_manifest_path = PIPELINE / "implementation_extrapolated_arrival_curve_module_manifest.json"
    dep_manifest = read_json(dep_manifest_path)
    dep_status = read_json(PIPELINE / "implementation_extrapolated_arrival_curve_module_status.json")
    require(dep_status["per_file"]["implementation/definitions/extrapolated_arrival_curve.v"]["status"]
            == "ACCEPTED_V06_FILE", "Rank 33 operation dependency not accepted")
    dep_cert = PROJECT / "Validation/certificates/implementation/ExtrapolatedArrivalCurveFullCorrespondence.v"
    require(sha(dep_cert) == dep_manifest["artifact_hashes"]["certificate_source_sha256"],
            "accepted Rank 33 operation certificate changed")
    generated_adapter = WORK / "certificates/ExtrapolatedArrivalCurveFactsOperationAdapter.v"
    require(dep_manifest["artifact_hashes"]["certificate_source_sha256"]
            in generated_adapter.read_text()
            and "Sole substitution: ImportedExtrapolatedArrivalCurve -> " + IMPORTED
            in generated_adapter.read_text(), "adapter was not generated from accepted source")
    require(sha(PROJECT / "Prosa/Implementation/Definitions/ExtrapolatedArrivalCurve.lean")
            == dep_manifest["artifact_hashes"]["production_source_sha256"],
            "Rank 33 production dependency changed")
    all_manifest = read_json(PIPELINE / "util_all_module_manifest.json")
    all_status = read_json(PIPELINE / "util_all_module_status.json")
    require(all_manifest["acceptance"] == "ACCEPTED_V06_FILE"
            and all_status["status"] == "PASS"
            and sha(PROJECT / "Prosa/Util/All.lean")
            == all_manifest["production_source_sha256"],
            "util/all.v dependency not accepted/current")
    time_manifest = read_json(PIPELINE / "foundation_slice_1_manifest.json")
    require(time_manifest["authoritative_source"]["commit"] == PIN
            and time_manifest["authoritative_source"]["sha256"]
            == sha(SOURCE / "behavior/time.v")
            and time_manifest["artifacts"]["lean_source_sha256"]
            == sha(PROJECT / "Prosa/Behavior/Time.lean")
            and {item.get("rocq_declaration", "") for item in time_manifest["declarations"]}
            == {"prosa.behavior.time.duration", "prosa.behavior.time.instant"}
            and all(item["acceptance"] == "ACCEPTED_V06_TRANSLATION"
                    for item in time_manifest["declarations"]),
            "behavior/time.v dependency evidence absent")

    require("Lean (version 4.33.1" in cmd("lake", "env", "lean", "--version"),
            "Lean toolchain changed")
    require(cmd("git", "-C", str(PROJECT / ".lake/packages/mathlib"), "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474",
            "Mathlib revision changed")
    rocq_version = cmd("opam", "exec", "--switch=rocq93rc1", "--", "rocq", "--version")
    require("9.3" in rocq_version, "Rocq importer environment changed")

    source_meta = read_json(WORK / "source_metadata.json")
    replay_meta = read_json(WORK / "source_metadata_regenerated.json")
    require(source_meta["source_commit"] == PIN
            and source_meta["source_file_sha256"] == source_sha
            and source_meta["declarations"] == replay_meta["declarations"]
            and sha(WORK / "source/OfficialExtrapolatedArrivalCurveFacts.v")
            == sha(WORK / "source/OfficialExtrapolatedArrivalCurveFactsRegenerated.v"),
            "source extraction not reproducible")
    elaborated = read_json(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for name in targets:
        record = source_meta["declarations"][name]
        evidence = elaborated[f"prosa.{SOURCE_FILE[:-2].replace('/', '.')}.{name}"]
        rendered_type = evidence["normalized_check"].split(":", 1)[1].strip()
        require(record["acquisition_mode"] == "STATEMENT_EXACT_PROOF_OMITTED"
                and record["statement_sort"] == "Prop"
                and record["elaborated_type_evidence"] == "ELABORATED_ROCQ_CHECK"
                and record["elaborated_type_sha256"]
                == hashlib.sha256(rendered_type.encode()).hexdigest(),
                f"source post-Section statement fidelity failed: {name}")

    production = PROJECT / "Prosa/Implementation/Facts/ExtrapolatedArrivalCurve.lean"
    project_olean = PROJECT / ".lake/build/lib/lean/Prosa/Implementation/Facts/ExtrapolatedArrivalCurve.olean"
    isolated_olean = WORK / "olean/Prosa/Implementation/Facts/ExtrapolatedArrivalCurve.olean"
    wrapper_source = PROJECT / "Validation/fixtures/translation_order/ExtrapolatedArrivalCurveFactsExportInterface.lean"
    wrapper_olean = PROJECT / ".lake/build/lib/lean/Validation/fixtures/translation_order/ExtrapolatedArrivalCurveFactsExportInterface.olean"
    for path in (production, project_olean, isolated_olean, wrapper_source, wrapper_olean):
        sha(path)
    require(production.stat().st_mtime_ns < project_olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns,
            "actual exported olean predates frozen production source or wrapper")
    lean_log = (WORK / "lean_proof_audit.log").read_text()
    require("sorryAx" not in lean_log and "error:" not in lean_log,
            "Lean proof audit reports error/sorry")
    axioms = dict(re.findall(
        rf"'({re.escape(MODULE)}\.[A-Za-z0-9_]+)' depends on axioms: \[([^\]]*)\]",
        lean_log, re.S))
    require(set(axioms) == {f"{MODULE}.{name}" for name in targets},
            "Lean #print axioms coverage is incomplete")
    for name, evidence in axioms.items():
        actual = {part.strip() for part in evidence.split(",") if part.strip()}
        require(actual <= {"propext", "Quot.sound", "Classical.choice"},
                f"unexpected Lean proof axiom: {name}: {actual}")

    config_path = PROJECT / "Validation/tooling/implementation_facts_extrapolated_arrival_curve_combined_export_config.json"
    config = read_json(config_path)
    export_meta = read_json(WORK / "combined_export_metadata.json")
    export_path = WORK / "ExtrapolatedArrivalCurveFactsCombined.out"
    require(config["module"] == "Validation.fixtures.translation_order.ExtrapolatedArrivalCurveFactsExportInterface"
            and config["statement_only"] == [f"{MODULE}.{name}" for name in targets]
            and len(config["definition_targets"]) == 21
            and len(config["body_theorems"]) == 4
            and export_meta["config_sha256"] == sha(config_path)
            and export_meta["output_sha256"] == sha(export_path)
            and export_meta["statement_only_count"] == 10,
            "actual compiled Lean export/config mismatch")
    imported_source = WORK / f"{IMPORTED}.v"
    require(f'Lean Import "Validation/.work/experiments/implementation_facts_extrapolated_arrival_curve/ExtrapolatedArrivalCurveFactsCombined.out".'
            in imported_source.read_text(), "imported Rocq module points to wrong export")

    cert = PROJECT / "Validation/certificates/implementation/ExtrapolatedArrivalCurveFactsCorrespondence.v"
    guards = PROJECT / "Validation/certificates/implementation/ExtrapolatedArrivalCurveFactsExactTypeGuards.v"
    audit_source = PROJECT / "Validation/certificates/implementation/ExtrapolatedArrivalCurveFactsAssumptionAudit.v"
    for path in (production, cert, guards, audit_source, generated_adapter):
        body = path.read_text()
        require(not any(token in body for token in ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden proof placeholder/axiom in {path}")
    guard_text = guards.read_text()
    require(all(f"source_guard_{name}" in guard_text and f"target_guard_{name}" in guard_text
                and f"{IMPORTED}.Prosa_Implementation_Facts_ExtrapolatedArrivalCurve_{name}"
                not in cert.read_text() for name in targets),
            "source/target exact-type guards or semantic self-independence missing")
    audit = read_json(WORK / "assumption_summary.json")
    require(audit["audit_policy"] == "fail_closed" and set(audit["certificates"]) == set(targets),
            "fail-closed assumption audit incomplete")
    for name, record in audit["certificates"].items():
        require(record["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and not record["semantic_premises"]
                and not record["statement_only_dependencies"]
                and not record["source_theorem_dependency"]
                and not record["target_theorem_dependency"]
                and not record["unexpected"], f"certificate assumption audit failed: {name}")
    require(not cmd("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")

    artifacts = {
        "source_signature": WORK / "source/OfficialExtrapolatedArrivalCurveFacts.v",
        "source_signature_vo": WORK / "source/OfficialExtrapolatedArrivalCurveFacts.vo",
        "source_metadata": WORK / "source_metadata.json",
        "source_replay_metadata": WORK / "source_metadata_regenerated.json",
        "source_type_evidence": PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json",
        "production_source": production,
        "production_olean": project_olean,
        "isolated_compilation_olean": isolated_olean,
        "export_wrapper_source": wrapper_source,
        "export_wrapper_olean": wrapper_olean,
        "accepted_operation_dependency_manifest": dep_manifest_path,
        "generated_operation_adapter": generated_adapter,
        "generated_operation_adapter_vo": WORK / "certificates/ExtrapolatedArrivalCurveFactsOperationAdapter.vo",
        "export_config": config_path,
        "export": export_path,
        "imported_source": imported_source,
        "imported_vo": WORK / f"{IMPORTED}.vo",
        "correspondence_source": cert,
        "correspondence_vo": cert.with_suffix(".vo"),
        "exact_type_guard_source": guards,
        "exact_type_guard_vo": guards.with_suffix(".vo"),
        "assumption_audit_source": audit_source,
        "assumption_audit_vo": audit_source.with_suffix(".vo"),
        "assumption_config": PROJECT / "Validation/certificates/implementation/extrapolated_arrival_curve_facts_assumption_config.json",
        "assumption_summary": WORK / "assumption_summary.json",
        "lean_proof_audit": WORK / "lean_proof_audit.log",
    }
    hashes = {name + "_sha256": sha(path) for name, path in artifacts.items()}
    snapshot = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        record = audit["certificates"][name]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": f"{MODULE}.{name}",
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_block_sha256": source_meta["declarations"][name]["source_block_sha256"],
            "source_elaborated_type_sha256": source_meta["declarations"][name]["elaborated_type_sha256"],
            "semantic_status": record["status"],
            "semantic_certificate": record["certificate"],
            "semantic_premises": [],
            "statement_only_dependencies": [],
            "prop_sprop_foundation": record["prop_sprop_foundation"],
            "unexpected_assumptions": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": "TRANSLATION_ORDER_IMPLEMENTATION_FACTS_EXTRAPOLATED_ARRIVAL_CURVE",
        "generated_at": datetime.now().astimezone().isoformat(),
        "source_file": SOURCE_FILE,
        "source_commit": PIN,
        "source_file_sha256": source_sha,
        "production_file": "Prosa/Implementation/Facts/ExtrapolatedArrivalCurve.lean",
        "lean_version": "4.33.1",
        "mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
        "rocq_version": rocq_version,
        "export_mode": "ten exact compiled target theorem types statement-only; 21 accepted computation bodies; four proof-bodied arithmetic interfaces",
        "snapshot_id": snapshot,
        "artifact_hashes": hashes,
        "declarations": declarations,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = PIPELINE / "implementation_facts_extrapolated_arrival_curve_module_manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": manifest["slice"],
        "per_file": {SOURCE_FILE: {
            "public_declarations": 10, "translated": 10, "proof_clean": 10,
            "certified": 10, "certified_without_prop_sprop_foundation": 0,
            "certified_with_prop_sprop_foundation": 10,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": {"accepted_files": 35, "authoritative_files": 357,
                     "accepted_declarations": 316, "authoritative_declarations": 2439,
                     "translated_but_not_certified": 0, "deferred_external_boundary": 239},
        "previous_status_sha256": sha(previous_path),
        "manifest_sha256": sha(manifest_path),
        "snapshot_id": snapshot,
        "status": "PASS",
    }
    (PIPELINE / "implementation_facts_extrapolated_arrival_curve_module_status.json").write_text(
        json.dumps(status, indent=2) + "\n")
    print("PUBLISHED implementation/facts/extrapolated_arrival_curve.v: 10/10; cumulative 316/2439, 35/357")


if __name__ == "__main__":
    main()
