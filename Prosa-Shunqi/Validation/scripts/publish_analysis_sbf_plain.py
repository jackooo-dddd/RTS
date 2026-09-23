#!/usr/bin/env python3
"""Fail-closed publication for pinned analysis/definitions/sbf/plain.v."""

from __future__ import annotations

import csv
import hashlib
import json
import re
import subprocess
from datetime import datetime, timedelta, timezone
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
PIPELINE = PROJECT / "Validation/planning/v06_pipeline"
WORK = PROJECT / "Validation/.work/experiments/analysis_sbf_plain"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE_FILE = "analysis/definitions/sbf/plain.v"
MODULE = "Prosa.Analysis.Definitions.Sbf.Plain"
NAMES = ["supply_bound_function_respected", "valid_supply_bound_function",
         "sbf_respected_simplified"]
CERTS = ["plain_supply_bound_function_respected_correspondence",
         "plain_valid_supply_bound_function_correspondence",
         "plain_sbf_respected_simplified_statement_correspondence"]
REPLAY = ["SupplyBaseAdapter", "SupplyScheduleBaseAdapter",
          "SupplyScheduleFiniteOperations", "SupplyScheduleOperations",
          "SupplyNatBoolOperations", "SupplyIntervalOperations",
          "SupplyCorrespondence", "ArrivalSequenceBaseAdapter",
          "ArrivalSequenceOperations", "ArrivalSequenceCorrespondence",
          "PredCorrespondence"]


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise SystemExit(reason)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    sha(path)
    return json.loads(path.read_text())


def cmd(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read(PIPELINE / "analysis_sbf_plain_selection.json")
    require(selection["rank"] == 43 and selection["file_dag_ready"]
            and selection["source_file"] == SOURCE_FILE
            and selection["targets_in_source_order"] == NAMES,
            "rank/file-DAG/inventory selection mismatch")
    source_root = PROJECT / "Validation/.work/prosa-v06-414e667"
    require(cmd("git", "-C", str(source_root), "rev-parse", "HEAD") == PIN
            and not cmd("git", "-C", str(source_root), "status", "--porcelain"),
            "official source not pinned/clean")
    official = source_root / SOURCE_FILE
    require(sha(official) == selection["source_sha256"], "pinned source changed")
    source_copy = WORK / "source" / SOURCE_FILE
    old = "    by apply: (SUP _ _ t2) => //; lia.\n"
    new = "    apply: (SUP j t1 t2 ARR I t2).\n    by rewrite leqnn andbT.\n"
    require(official.read_text().count(old) == 1
            and source_copy.read_text() == official.read_text().replace(old, new, 1),
            "source compatibility copy changed a public statement/body")
    patch = PROJECT / "Validation/patches/prosa-v06-rocq93-analysis-sbf-plain.patch"
    require(SOURCE_FILE in cmd("patch", "--dry-run", "--forward", "-p1", "-d",
                               str(source_root), "-i", str(patch)),
            "Rocq 9.3 proof-only patch does not apply to pinned source")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE_FILE]
    require([r["declaration_name"] for r in rows] == NAMES
            and [r["kind"] for r in rows] == ["Definition", "Definition", "Remark"],
            "public inventory mismatch")
    types = read(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + types[row["qualified_name"]]["sha256"],
                f"elaborated source type mismatch: {row['declaration_name']}")
    previous = read(PIPELINE / "analysis_service_module_status.json")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 41
            and previous["coverage"]["accepted_declarations"] == 333,
            "previous publication baseline invalid")
    for name in ("analysis_sbf_pred", "util_all"):
        path = PIPELINE / f"{name}_module_manifest.json"
        manifest = read(path)
        require(manifest["acceptance"] == "ACCEPTED_V06_FILE"
                and sha(PROJECT / manifest["production_file"])
                == manifest["production_source_sha256"],
                f"accepted file prerequisite stale: {name}")
    pred = read(PIPELINE / "analysis_sbf_pred_module_manifest.json")
    require(sha(WORK / "olean/Prosa/Analysis/Definitions/Sbf/Pred.olean")
            == pred["production_olean_sha256"], "reused Pred .olean changed")
    require("Lean (version 4.33.1" in cmd("lake", "env", "lean", "--version")
            and cmd("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in cmd("opam", "exec", "--switch=rocq93rc1", "--",
                             "rocq", "--version"),
            "toolchain version mismatch")
    tooling = read(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tool identity mismatch")

    production = PROJECT / "Prosa/Analysis/Definitions/Sbf/Plain.lean"
    olean = WORK / "olean/Prosa/Analysis/Definitions/Sbf/Plain.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/PlainExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/PlainExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "compiled target or export root stale")
    lean_log = WORK / "lean_audit.log"
    lean_text = lean_log.read_text()
    require("error:" not in lean_text and "sorryAx" not in lean_text,
            "Lean proof-clean audit failed")
    for name in NAMES:
        match = re.search(r"'" + re.escape(MODULE + "." + name)
                          + r"' depends on axioms: \[([^\]]*)\]", lean_text, re.S)
        require(match is not None and {s.strip() for s in match.group(1).split(",")}
                <= {"propext", "Classical.choice", "Quot.sound"},
                f"unexpected Lean axiom: {name}")
    config_path = PROJECT / "Validation/tooling/analysis_sbf_plain_export_config.json"
    config = read(config_path)
    export = WORK / "Plain.out"
    metadata = read(WORK / "export_metadata.json")
    require(config["module"] == "Validation.fixtures.translation_order.PlainExportInterface"
            and all(MODULE + "." + n in config["definition_targets"] for n in NAMES[:2])
            and MODULE + ".sbf_respected_simplified" in config["statement_only"]
            and metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 2
            and len(metadata["normalization"]["body_projections"]) == 5,
            "compiled export configuration/artifact changed")
    imported = WORK / "ImportedPlain.v"
    imported_vo = WORK / "ImportedPlain.vo"
    require('Lean Import "Validation/.work/experiments/analysis_sbf_plain/Plain.out".'
            in imported.read_text()
            and export.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "imported artifact stale/wrong export")
    cert = PROJECT / "Validation/certificates/analysis/PlainCorrespondence.v"
    guard = PROJECT / "Validation/certificates/analysis/PlainExactTypeGuards.v"
    audit = PROJECT / "Validation/certificates/analysis/PlainAssumptionAudit.v"
    audit_config = PROJECT / "Validation/certificates/analysis/plain_assumption_config.json"
    for path in (production, cert, guard, audit):
        require(not any(token in path.read_text() for token in
                        ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden escape: {path}")
    proof = cert.read_text()
    require(all("prosa.analysis.definitions.sbf.plain." + n in proof
                and "ImportedPlain.Prosa_Analysis_Definitions_Sbf_Plain_" + n in proof
                for n in NAMES[:2])
            and "pred_sbf_respected_correspondence" in proof
            and "pred_valid_pred_sbf_correspondence" in proof
            and "plain_true_predicate_relation" in proof
            and "arrives_in_correspondence_certificate" in proof
            and "supply_during_correspondence" in proof
            and "PlainExactTypeGuards" not in proof
            and "plain.sbf_respected_simplified" not in proof
            and "Plain_sbf_respected_simplified" not in proof,
            "structural statement proof missing or circular")
    work_cert = WORK / "certificates/PlainCorrespondence.v"
    work_guard = WORK / "certificates/PlainExactTypeGuards.v"
    work_audit = WORK / "certificates/PlainAssumptionAudit.v"
    for original, copy in ((cert, work_cert), (guard, work_guard), (audit, work_audit)):
        require(sha(original) == sha(copy)
                and copy.stat().st_mtime_ns < copy.with_suffix(".vo").stat().st_mtime_ns,
                f"Rocq certificate/type guard/audit stale: {original}")
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "assumption audit policy changed")
    for key in ["plain_true", *NAMES]:
        record = summary["certificates"][key]
        require(record["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and record["prop_sprop_foundation"] ==
                ["PropSPropFoundation.interpret_strict"]
                and not record["semantic_premises"]
                and not record["statement_only_dependencies"]
                and not record["source_theorem_dependency"]
                and not record["target_theorem_dependency"]
                and not record["unexpected"],
                f"unclean assumption closure: {key}")
    require(not cmd("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")
    artifacts = {
        "compatibility_patch": patch, "source_copy": source_copy,
        "source_vo": source_copy.with_suffix(".vo"),
        "source_inspection_vo": WORK / "PlainSourceInspection.vo",
        "target_inspection_vo": WORK / "PlainImportedInspection.vo",
        "production_source": production, "production_olean": olean,
        "wrapper_source": wrapper, "wrapper_olean": wrapper_olean,
        "lean_audit_log": lean_log, "export_config": config_path,
        "export_metadata": WORK / "export_metadata.json", "export": export,
        "imported_source": imported, "imported_vo": imported_vo,
        "certificate_source": cert, "certificate_vo": work_cert.with_suffix(".vo"),
        "guard_source": guard, "guard_vo": work_guard.with_suffix(".vo"),
        "audit_source": audit, "audit_vo": work_audit.with_suffix(".vo"),
        "audit_config": audit_config, "assumption_summary": WORK / "assumption_summary.json",
    }
    for name in REPLAY:
        path = WORK / f"certificates/{name}.v"
        source_dir = ("analysis" if name == "PredCorrespondence" else
                      "model_processor_supply" if name.startswith("Supply") else
                      "behavior_arrival_sequence")
        producer = PROJECT / f"Validation/certificates/{source_dir}/{name}.v"
        require(sha(producer) in path.read_text()
                and "ImportedPlain" in path.read_text()
                and path.stat().st_mtime_ns < path.with_suffix(".vo").stat().st_mtime_ns,
                f"replayed bridge not bound to imported artifact: {name}")
        artifacts[f"replayed_{name}_source"] = path
        artifacts[f"replayed_{name}_vo"] = path.with_suffix(".vo")
    hashes = {key + "_sha256": sha(path) for key, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_SBF_PLAIN", "source_commit": PIN,
        "source_file": SOURCE_FILE, "source_file_sha256": sha(official),
        "source_compatibility": "proof-only Rocq 9.3 patch; public statements and computational bodies identical",
        "production_file": "Prosa/Analysis/Definitions/Sbf/Plain.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": MODULE + "." + name,
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": types[row["qualified_name"]]["sha256"],
            "semantic_certificate": CERTS[i],
            "semantic_status": summary["certificates"][name]["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION",
        } for i, (name, row) in enumerate(zip(NAMES, rows))],
        "artifact_hashes": hashes,
        "tooling_manifest_sha256": sha(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE_FILE: {
            "public_declarations": 3, "translated": 3, "proof_clean": 3,
            "certified": 3, "certified_without_prop_sprop_foundation": 0,
            "certified_with_prop_sprop_foundation": 3,
            "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**previous["coverage"], "accepted_files": 42,
                     "accepted_declarations": 336,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPELINE / "analysis_sbf_plain_module_manifest.json"
    status_path = PIPELINE / "analysis_sbf_plain_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "declarations": 3, "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
