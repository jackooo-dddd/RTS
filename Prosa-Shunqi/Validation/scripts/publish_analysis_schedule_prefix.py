#!/usr/bin/env python3
"""Fail-closed Rank 44 publication for pinned schedule_prefix.v."""

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
WORK = PROJECT / "Validation/.work/experiments/analysis_schedule_prefix"
SOURCE = "analysis/definitions/schedule_prefix.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
MODULE = "Prosa.Analysis.Definitions.SchedulePrefix"
NAMES = ["identical_prefix", "identical_prefix_scheduled_at",
         "identical_prefix_inclusion"]
CERTS = ["identical_prefix_correspondence",
         "identical_prefix_scheduled_at_statement_correspondence",
         "identical_prefix_inclusion_statement_correspondence"]
EXPECTED_STATUSES = {name: "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                     for name in NAMES}
EXPECTED_STATUSES.update({"scheduled_in_dependency": "CERTIFIED",
                          "scheduled_at_dependency": "CERTIFIED"})


def require(condition: bool, reason: str) -> None:
    if not condition:
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
    selection = read(PIPELINE / "analysis_schedule_prefix_selection.json")
    require(selection["rank"] == 44 and selection["file_dag_ready"]
            and selection["source_file"] == SOURCE
            and selection["targets_in_source_order"] == NAMES,
            "rank/file DAG/source inventory selection mismatch")
    source_root = PROJECT / "Validation/.work/prosa-v06-414e667"
    require(cmd("git", "-C", str(source_root), "rev-parse", "HEAD") == PIN
            and not cmd("git", "-C", str(source_root), "status", "--porcelain"),
            "pinned official source dirty/wrong commit")
    official = source_root / SOURCE
    require(sha(official) == selection["source_sha256"],
            "official source hash changed")
    source_copy = WORK / "source" / SOURCE
    old = "  Proof. by move=> sched sched' h h' h'_le_h + t t_lt_h'; apply; apply: leq_trans h'_le_h. Qed.\n"
    new = ("  Proof.\n"
           "    move=> sched sched' h h' h'_le_h PREFIX t t_lt_h'.\n"
           "    apply: PREFIX.\n"
           "    exact: (ltn_leq_trans t_lt_h' h'_le_h).\n"
           "  Qed.\n")
    require(official.read_text().count(old) == 1
            and source_copy.read_text() == official.read_text().replace(old, new, 1),
            "Rocq 9.3 copy changed a declaration statement/body")
    patch = PROJECT / "Validation/patches/prosa-v06-rocq93-analysis-schedule-prefix.patch"
    require(SOURCE in cmd("patch", "--dry-run", "--forward", "-p1", "-d",
                          str(source_root), "-i", str(patch)),
            "compatibility patch not applicable to pinned source")

    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as f:
        rows = [r for r in csv.DictReader(f) if r["source_file"] == SOURCE]
    require([r["declaration_name"] for r in rows] == NAMES
            and [r["kind"] for r in rows] == ["Definition", "Fact", "Fact"],
            "declaration inventory mismatch")
    types = read(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + types[row["qualified_name"]]["sha256"],
                "official elaborated type evidence mismatch")
    previous = read(PIPELINE / "analysis_sbf_plain_module_status.json")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 42
            and previous["coverage"]["accepted_declarations"] == 336,
            "previous published baseline changed")
    ready = read(PIPELINE / "behavior_ready_module_manifest.json")
    require(ready["acceptance"] == "ACCEPTED_V06_FILE"
            and sha(PROJECT / ready["production_file"]) ==
            ready["production_source_sha256"]
            and sha(WORK / "olean/Prosa/Behavior/Ready.olean") ==
            ready["production_olean_sha256"], "Ready dependency not hash-accepted")
    utility = read(PIPELINE / "utility_foundation_expansion_manifest.json")
    utility_status = read(PIPELINE / "utility_foundation_expansion_status.json")
    nat = [d for d in utility["declarations"] if d.get("source_file") == "util/nat.v"]
    require(len(nat) == 2 and utility_status["per_file"]["util/nat.v"]["status"]
            == "ACCEPTED_V06_FILE"
            and all(d["fresh_olean_sha256"] ==
                    sha(WORK / "olean/Prosa/Util/Nat.olean") for d in nat),
            "Nat dependency not hash-accepted")
    require("Lean (version 4.33.1" in cmd("lake", "env", "lean", "--version")
            and cmd("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                    "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in cmd("opam", "exec", "--switch=rocq93rc1", "--",
                             "rocq", "--version"), "toolchain mismatch")
    tooling = read(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Analysis/Definitions/SchedulePrefix.lean"
    olean = WORK / "olean/Prosa/Analysis/Definitions/SchedulePrefix.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/SchedulePrefixExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/SchedulePrefixExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "Lean source/compiled export root stale")
    lean_audit = WORK / "lean_audit.log"
    lean_text = lean_audit.read_text()
    require("error:" not in lean_text and "sorryAx" not in lean_text
            and all(MODULE + "." + name in lean_text for name in NAMES),
            "Lean audit missing/failed")
    for name in NAMES[1:]:
        match = re.search(r"'" + re.escape(MODULE + "." + name)
                          + r"' depends on axioms: \[([^\]]*)\]", lean_text, re.S)
        require(match is not None and
                {re.sub(r"\.\{[^}]*\}$", "", s.strip())
                 for s in match.group(1).split(",")}
                <= {"propext", "Classical.choice", "Quot.sound"},
                f"Lean proof not clean: {name}")
    config_path = PROJECT / "Validation/tooling/analysis_schedule_prefix_export_config.json"
    config = read(config_path)
    export = WORK / "SchedulePrefix.out"
    metadata = read(WORK / "export_metadata.json")
    require(config["module"] ==
            "Validation.fixtures.translation_order.SchedulePrefixExportInterface"
            and set(MODULE + "." + n for n in NAMES[1:])
            == set(config["statement_only"])
            and MODULE + ".identical_prefix" in config["definition_targets"]
            and metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 2
            and len(metadata["normalization"]["body_projections"]) == 1,
            "export artifact/config/guard mismatch")
    imported = WORK / "imported/ImportedSchedulePrefix.v"
    imported_vo = WORK / "imported/ImportedSchedulePrefix.vo"
    require('Lean Import "Validation/.work/experiments/analysis_schedule_prefix/SchedulePrefix.out".'
            in imported.read_text()
            and export.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "imported Rocq artifact stale/wrong")
    cert = PROJECT / "Validation/certificates/analysis/SchedulePrefixOperations.v"
    guard = PROJECT / "Validation/certificates/analysis/SchedulePrefixExactTypeGuards.v"
    audit = PROJECT / "Validation/certificates/analysis/SchedulePrefixAssumptionAudit.v"
    audit_config = PROJECT / "Validation/certificates/analysis/schedule_prefix_assumption_config.json"
    for path in (production, cert, guard, audit):
        require(not any(token in path.read_text() for token in
                        ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden proof escape: {path}")
    cert_text = cert.read_text()
    require("ImportedSchedulePrefix.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix"
            in cert_text
            and "prosa.analysis.definitions.schedule_prefix.identical_prefix"
            in cert_text
            and "prefix_scheduled_in_related" in cert_text
            and "prefix_scheduled_at_related" in cert_text,
            "correspondence target/operation binding missing")
    for path in (cert, guard, audit):
        copy = WORK / "certificates" / path.name
        require(sha(path) == sha(copy)
                and copy.stat().st_mtime_ns < copy.with_suffix(".vo").stat().st_mtime_ns,
                f"certificate/guard/audit stale: {path}")
    require("identical_prefix_scheduled_at" in (WORK / "SchedulePrefixExactTypeGuards.log").read_text(),
            "source/imported theorem type guards not executed")
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "audit not fail-closed")
    for key, expected in EXPECTED_STATUSES.items():
        rec = summary["certificates"][key]
        require(rec["status"] == expected
                and not rec["semantic_premises"]
                and not rec["statement_only_dependencies"]
                and not rec["unexpected"]
                and not rec["source_theorem_dependency"]
                and not rec["target_theorem_dependency"],
                f"unclean semantic assumption closure: {key}")
    require(not cmd("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")

    artifacts = {
        "compatibility_patch": patch, "source_copy": source_copy,
        "source_vo": source_copy.with_suffix(".vo"),
        "production_source": production, "production_olean": olean,
        "wrapper_source": wrapper, "wrapper_olean": wrapper_olean,
        "lean_audit_log": lean_audit, "export_config": config_path,
        "export_metadata": WORK / "export_metadata.json", "export": export,
        "imported_source": imported, "imported_vo": imported_vo,
        "certificate_source": cert,
        "certificate_vo": WORK / "certificates/SchedulePrefixOperations.vo",
        "guard_source": guard,
        "guard_vo": WORK / "certificates/SchedulePrefixExactTypeGuards.vo",
        "audit_source": audit,
        "audit_vo": WORK / "certificates/SchedulePrefixAssumptionAudit.vo",
        "audit_config": audit_config,
        "assumption_summary": WORK / "assumption_summary.json",
        "accepted_ready_olean": WORK / "olean/Prosa/Behavior/Ready.olean",
        "accepted_nat_olean": WORK / "olean/Prosa/Util/Nat.olean",
    }
    hashes = {key + "_sha256": sha(path) for key, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_SCHEDULE_PREFIX", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": sha(official),
        "source_compatibility": "proof-only Rocq 9.3 patch; statements/bodies identical",
        "production_file": "Prosa/Analysis/Definitions/SchedulePrefix.lean",
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
            "input_relations": ["PrefixProcessorRel two-sided state/core map",
                                "PrefixScheduleRel canonical pointwise map"],
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
        "per_file": {SOURCE: {
            "public_declarations": 3, "translated": 3, "proof_clean": 3,
            "certified": 3, "certified_without_prop_sprop_foundation": 0,
            "certified_with_prop_sprop_foundation": 3,
            "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**previous["coverage"], "accepted_files": 43,
                     "accepted_declarations": 339,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPELINE / "analysis_schedule_prefix_module_manifest.json"
    status_path = PIPELINE / "analysis_schedule_prefix_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "declarations": 3, "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
