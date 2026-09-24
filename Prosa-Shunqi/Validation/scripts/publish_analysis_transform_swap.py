#!/usr/bin/env python3
"""Fail-closed publication of the pinned two-definition swap file."""

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
PIPE = PROJECT / "Validation/planning/v06_pipeline"
WORK = PROJECT / "Validation/.work/experiments/analysis_transform_swap"
PRODUCER = PROJECT / "Validation/.work/runs/behavior_all_finalize.djIKMA"
SOURCE = "analysis/transform/swap.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
NAMES = ("replace_at", "swapped")


def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit(message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read(PIPE / "analysis_transform_swap_selection.json")
    require(selection["rank"] == 46 and selection["source_file"] == SOURCE
            and selection["file_dag_ready"]
            and selection["targets_in_source_order"] == list(NAMES)
            and selection["direct_internal_dependencies"] == ["behavior/all.v"],
            "selection/DAG mismatch")
    source_root = PROJECT / "Validation/.work/prosa-v06-414e667"
    official = source_root / SOURCE
    source_copy = WORK / "source" / SOURCE
    require(command("git", "-C", str(source_root), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(source_root), "status", "--porcelain")
            and sha(official) == selection["source_sha256"]
            and sha(source_copy) == sha(official), "official source mismatch")
    with (PROJECT / "Validation/planning/v06_dependency/declaration_inventory.csv").open() as f:
        rows = [r for r in csv.DictReader(f) if r["source_file"] == SOURCE]
    require([r["declaration_name"] for r in rows] == list(NAMES)
            and all(r["kind"] == "Definition" for r in rows),
            "declaration inventory mismatch")
    evidence = read(PROJECT / "Validation/planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + evidence[row["qualified_name"]]["sha256"],
                f"elaborated source type mismatch: {row['declaration_name']}")
    previous = read(PIPE / "analysis_job_response_time_module_status.json")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 44
            and previous["coverage"]["accepted_declarations"] == 340,
            "published baseline changed")
    accepted_all = read(PIPE / "behavior_all_module_manifest.json")
    require(accepted_all["acceptance"] == "ACCEPTED_V06_FILE"
            and accepted_all["source_commit"] == PIN
            and sha(PROJECT / accepted_all["production_file"]) ==
                accepted_all["production_source_sha256"]
            and sha(PRODUCER / "olean/Prosa/Behavior/All.olean") ==
                accepted_all["production_olean_sha256"],
            "Behavior.All producer invalidated")
    for tree in ("Prosa", "Validation"):
        for dependency in (PRODUCER / "olean" / tree).rglob("*.olean"):
            relative = dependency.relative_to(PRODUCER / "olean")
            require(sha(dependency) == sha(WORK / "olean" / relative),
                    f"accepted dependency changed: {relative}")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version")
            and command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                        "rev-parse", "HEAD") ==
                "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                                 "rocq", "--version"), "toolchain mismatch")
    tooling = read(PROJECT / "Validation/tooling/tooling_manifest.json")
    require(sha(PROJECT / "Validation/.work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(PROJECT / "Validation/.work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "tooling mismatch")
    production = PROJECT / "Prosa/Analysis/Transform/Swap.lean"
    olean = WORK / "olean/Prosa/Analysis/Transform/Swap.olean"
    wrapper = PROJECT / "Validation/fixtures/translation_order/SwapExportInterface.lean"
    wrapper_olean = WORK / "olean/Validation/fixtures/translation_order/SwapExportInterface.olean"
    require(production.stat().st_mtime_ns < olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns, "stale Lean snapshot")
    lean_audit = WORK / "lean_audit.log"
    text = lean_audit.read_text()
    require("error:" not in text and "sorryAx" not in text
            and all("Prosa.Analysis.Transform.Swap." + name in text
                    for name in NAMES), "Lean proof/computation audit failed")
    for name in NAMES:
        target = "Prosa.Analysis.Transform.Swap." + name
        match = re.search(r"'" + re.escape(target) +
                          r"' depends on axioms: \[([^\]]*)\]", text, re.S)
        require(match is not None and {a.strip() for a in match.group(1).split(",")}
                <= {"propext", "Classical.choice", "Quot.sound"},
                f"Lean axiom audit failed: {name}")
    config_path = PROJECT / "Validation/tooling/analysis_transform_swap_export_config.json"
    config = read(config_path)
    export = WORK / "Swap.out"
    metadata = read(WORK / "export_metadata.json")
    require(config["module"] ==
            "Validation.fixtures.translation_order.SwapExportInterface"
            and config["definition_targets"] ==
                ["Prosa.Analysis.Transform.Swap." + n for n in NAMES]
            and metadata["config_sha256"] == sha(config_path)
            and metadata["output_sha256"] == sha(export)
            and metadata["statement_only_count"] == 0,
            "actual export mismatch")
    imported = WORK / "imported/ImportedSwap.v"
    imported_vo = WORK / "imported/ImportedSwap.vo"
    require('Lean Import "Validation/.work/experiments/analysis_transform_swap/Swap.out".'
            in imported.read_text()
            and export.stat().st_mtime_ns < imported_vo.stat().st_mtime_ns,
            "stale/wrong imported artifact")
    cert_dir = PROJECT / "Validation/certificates/analysis"
    cert_files = ("SwapNatEquality.v", "SwapCorrespondence.v",
                  "SwapExactTypeGuards.v", "SwapAssumptionAudit.v")
    for path in (production, *(cert_dir / n for n in cert_files)):
        require(not any(token in path.read_text() for token in
                        ("sorry", "Admitted", "admit.", "Axiom ")),
                f"forbidden escape: {path}")
    cert_text = (cert_dir / "SwapCorrespondence.v").read_text()
    require(all("ImportedSwap.Prosa_Analysis_Transform_Swap_" + n in cert_text
                and "prosa.analysis.transform.swap." + n in cert_text
                for n in NAMES)
            and "apply replace_at_correspondence" in cert_text,
            "certificate does not bind/compose actual declarations")
    for name in cert_files:
        path = cert_dir / name
        copy = WORK / "certificates" / name
        require(sha(path) == sha(copy)
                and copy.stat().st_mtime_ns < copy.with_suffix(".vo").stat().st_mtime_ns,
                f"stale certificate: {name}")
    guards = (WORK / "SwapExactTypeGuards.log").read_text()
    require(all("@" + n in guards and
                "Prosa_Analysis_Transform_Swap_" + n in guards for n in NAMES),
            "exact type guards missing")
    summary = read(WORK / "assumption_summary.json")
    require(summary["audit_policy"] == "fail_closed", "audit policy mismatch")
    for key in ("nat_equality_dependency", *NAMES):
        rec = summary["certificates"][key]
        require(rec["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and not rec["semantic_premises"]
                and not rec["statement_only_dependencies"]
                and not rec["source_theorem_dependency"]
                and not rec["target_theorem_dependency"]
                and not rec["unexpected"], f"assumption audit failed: {key}")
    require(not command("git", "-C", str(ROOT), "diff", "--check"),
            "git diff --check failed")
    artifacts = {"official_source": official, "source_copy": source_copy,
                 "source_vo": source_copy.with_suffix(".vo"),
                 "production_source": production, "production_olean": olean,
                 "export_wrapper": wrapper, "export_wrapper_olean": wrapper_olean,
                 "lean_audit": lean_audit, "export_config": config_path,
                 "export_metadata": WORK / "export_metadata.json", "export": export,
                 "imported_source": imported, "imported_vo": imported_vo,
                 "exact_type_log": WORK / "SwapExactTypeGuards.log",
                 "assumption_log": WORK / "assumption_audit.log",
                 "assumption_summary": WORK / "assumption_summary.json",
                 "assumption_config": cert_dir / "swap_assumption_config.json",
                 "behavior_all_manifest": PIPE / "behavior_all_module_manifest.json"}
    for name in cert_files:
        artifacts[name] = cert_dir / name
        artifacts[name.replace(".v", ".vo")] = WORK / "certificates" / name.replace(".v", ".vo")
    hashes = {key + "_sha256": sha(path) for key, path in artifacts.items()}
    manifest = {
        "slice": "ANALYSIS_TRANSFORM_SWAP", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": sha(official),
        "source_compatibility": "byte-identical official source; no patch",
        "production_file": "Prosa/Analysis/Transform/Swap.lean",
        "production_source_sha256": hashes["production_source_sha256"],
        "production_olean_sha256": hashes["production_olean_sha256"],
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Analysis.Transform.Swap." + name,
            "kind": "Definition", "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": evidence[row["qualified_name"]]["sha256"],
            "semantic_certificate": name + "_correspondence",
            "semantic_status": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
            "input_relations": ["SwapStateIso", "SwapStateRel", "SwapScheduleRel",
                                "SubNatRel"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [], "acceptance": "ACCEPTED_V06_TRANSLATION",
        } for name, row in zip(NAMES, rows)],
        "artifact_hashes": hashes,
        "tooling_manifest_sha256": sha(PROJECT / "Validation/tooling/tooling_manifest.json"),
        "generated_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {"public_declarations": 2, "translated": 2,
                              "proof_clean": 2, "certified": 2,
                              "certified_with_prop_sprop_foundation": 2,
                              "status": "ACCEPTED_V06_FILE"}},
        "coverage": {**previous["coverage"], "accepted_files": 45,
                     "accepted_declarations": 342,
                     "translated_but_not_certified": 0},
        "manifest_sha256": None,
    }
    manifest_path = PIPE / "analysis_transform_swap_module_manifest.json"
    status_path = PIPE / "analysis_transform_swap_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status["manifest_sha256"] = sha(manifest_path)
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"acceptance": manifest["acceptance"],
                      "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
