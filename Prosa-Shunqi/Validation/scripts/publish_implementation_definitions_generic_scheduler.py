#!/usr/bin/env python3
"""Fail-closed publication of pinned generic_scheduler.v from a merged snapshot."""

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
VALIDATION = PROJECT / "Validation"
PIPE = VALIDATION / "planning/v06_pipeline"
WORK = VALIDATION / ".work/experiments/implementation_definitions_generic_scheduler"
SOURCE = "implementation/definitions/generic_scheduler.v"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE_SHA = "f5ba1f9356249784ab8a5e4f3fc0fbcb46c25450a383e8e7de7c08425c40a497"
LEAN_SHA = "79d26c7bee1540683c0583d55e1b4b447e00883654ad746616a884d1d5459439"
OLEAN_SHA = "fb3842437368f3bf7cffd2382cf207b94107f1215aaf1b63bc178263a2f8b517"
EXPORT_SHA = "eda023ad79b505b0c2cf0ba9c1a4a4851aace4737742f4810531b412d27f7b32"
IMPORTED_SHA = "77bbf1c85e27116787c793af887919a5a2847a8b9e82dc63521b011f551b6f2d"
NAMES = ("PointwisePolicy", "empty_schedule", "schedule_up_to", "generic_schedule")
MODULES = (
    "GenericSchedulerBaseAdapter", "GenericSchedulerOperations",
    "GenericSchedulerRecursionEquations", "GenericSchedulerCorrespondence",
    "GenericSchedulerExactTypeGuards", "GenericSchedulerAssumptionAudit",
)


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise SystemExit("GENERIC_SCHEDULER_PUBLICATION_REJECTED: " + reason)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    require(path.is_file(), f"missing {path}")
    return json.loads(path.read_text())


def output(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    candidates = []
    for path in PIPE.glob("*_module_status.json"):
        item = read(path)
        if item.get("status") == "PASS":
            coverage = item.get("coverage", {})
            candidates.append((coverage.get("accepted_files", -1),
                               coverage.get("accepted_declarations", -1), path))
    require(bool(candidates), "no cumulative PASS status")
    maximum = max(candidates)
    require(sum(x[:2] == maximum[:2] for x in candidates) == 1,
            "ambiguous latest cumulative status")
    require(maximum[:2] >= (65, 459), "Rank 69 baseline missing")
    previous_path, previous = maximum[2], read(maximum[2])

    official_root = VALIDATION / ".work/prosa-v06-414e667"
    official = official_root / SOURCE
    source_copy = WORK / "source" / SOURCE
    require(output("git", "-C", str(official_root), "rev-parse", "HEAD") == PIN
            and not output("git", "-C", str(official_root), "status", "--porcelain",
                           "--untracked-files=all")
            and sha(official) == SOURCE_SHA and sha(source_copy) == SOURCE_SHA,
            "official source or source copy changed")
    with (VALIDATION / "planning/v06_dependency/file_inventory.csv").open() as stream:
        row = next(r for r in csv.DictReader(stream) if r["file"] == SOURCE)
    require(row["sha256"] == SOURCE_SHA and row["layer"] == "11",
            "file inventory changed")
    graph = read(VALIDATION / "planning/v06_dependency/file_dag.json")
    deps = {e["dependency_file"] for e in graph["edges"]
            if e["dependent_file"] == SOURCE}
    require(deps == {"analysis/transform/swap.v"}, "file DAG changed")
    with (VALIDATION / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    require(tuple(r["declaration_name"] for r in rows) == NAMES
            and all(r["final_type_or_type_fingerprint"].startswith("rocq-check-sha256:")
                    for r in rows), "declaration inventory changed")

    swap = read(PIPE / "analysis_transform_swap_module_manifest.json")
    require(swap["acceptance"] == "ACCEPTED_V06_FILE"
            and sha(PROJECT / swap["production_file"]) == swap["production_source_sha256"]
            and sha(WORK / "lean/Prosa/Analysis/Transform/Swap.olean") ==
                swap["production_olean_sha256"]
            and sha(WORK / "source/analysis/transform/swap.vo") ==
                swap["artifact_hashes"]["source_vo_sha256"],
            "accepted Swap dependency invalidated")
    require("Lean (version 4.33.1" in output("lake", "env", "lean", "--version")
            and output("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                       "rev-parse", "HEAD") ==
                "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in output("opam", "exec", "--switch=rocq93rc1", "--",
                                "rocq", "--version"), "toolchain changed")
    tooling = read(VALIDATION / "tooling/tooling_manifest.json")
    require(sha(VALIDATION / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Implementation/Definitions/GenericScheduler.lean"
    olean = WORK / "lean/Prosa/Implementation/Definitions/GenericScheduler.olean"
    lean_guard = VALIDATION / "fixtures/translation_order/GenericSchedulerLeanTypeAudit.lean"
    lean_guard_olean = WORK / "lean/GenericSchedulerLeanTypeAudit.olean"
    source_vo = WORK / "source/implementation/definitions/generic_scheduler.vo"
    source_guard = VALIDATION / "fixtures/translation_order/GenericSchedulerSourceTypeAudit.v"
    source_guard_vo = source_guard.with_suffix(".vo")
    require(sha(production) == LEAN_SHA and sha(olean) == OLEAN_SHA
            and sha(lean_guard) and sha(lean_guard_olean)
            and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
            and lean_guard_olean.stat().st_mtime_ns > lean_guard.stat().st_mtime_ns
            and sha(source_vo) and source_vo.stat().st_mtime_ns > source_copy.stat().st_mtime_ns
            and sha(source_guard) and sha(source_guard_vo)
            and source_guard_vo.stat().st_mtime_ns > source_vo.stat().st_mtime_ns
            and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text()),
            "fresh Lean/source compilation or proof freeze failed")
    lean_audit = WORK / "lean_axiom_audit.log"
    text = lean_audit.read_text()
    for name in NAMES:
        require(f"GenericScheduler.{name}' depends on axioms:" in text,
                f"missing Lean axiom check for {name}")
    require("sorryAx" not in text and "error:" not in text.lower()
            and all(x in text for x in ("propext", "Classical.choice", "Quot.sound")),
            "Lean proof-axiom audit failed")
    config = VALIDATION / "tooling/implementation_definitions_generic_scheduler_export_config.json"
    c = read(config)
    require(c["targets"] ==
            ["Prosa.Implementation.Definitions.GenericScheduler." + n for n in NAMES]
            and c["statement_only"] == [] and c["body_theorems"] == []
            and not any(c["normalization"].values()), "export policy changed")
    exported = WORK / "GenericSchedulerFull.out"
    imported_vo = WORK / "imported/ImportedGenericScheduler.vo"
    imported_v = WORK / "imported/ImportedGenericScheduler.v"
    require(sha(exported) == EXPORT_SHA
            and sha(WORK / "imported/GenericSchedulerFull.out") == EXPORT_SHA
            and sha(imported_vo) == IMPORTED_SHA
            and imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns
            and "Lean Import \"GenericSchedulerFull.out\"" in imported_v.read_text()
            and "Error:" not in (WORK / "import.log").read_text(),
            "fresh actual artifact export/import failed")

    controlled = VALIDATION / "certificates/implementation_definitions_generic_scheduler"
    cert_dir = WORK / "certificates"
    for name in MODULES:
        formal = controlled / f"{name}.v"
        copy = cert_dir / f"{name}.v"
        compiled = cert_dir / f"{name}.vo"
        require(sha(formal) == sha(copy) and sha(compiled)
                and compiled.stat().st_mtime_ns > copy.stat().st_mtime_ns
                and compiled.stat().st_mtime_ns > imported_vo.stat().st_mtime_ns
                and "Error:" not in (WORK / f"{name}.log").read_text()
                and not re.search(r"\b(Axiom|Admitted|admit|sorry)\b", formal.read_text()),
                f"certificate stale/unclean: {name}")
    summary = read(WORK / "assumption_audit.json")
    require(summary.get("audit_policy") == "fail_closed"
            and "AUDIT_END" in (WORK / "GenericSchedulerAssumptionAudit.log").read_text()
            and set(NAMES).issubset(summary.get("certificates", {})),
            "assumption audit missing/truncated")
    expected = {
        "PointwisePolicy": "CERTIFIED", "empty_schedule": "CERTIFIED",
        "schedule_up_to": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
        "generic_schedule": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
    }
    for name, status in expected.items():
        item = summary["certificates"][name]
        require(item["status"] == status
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"]
                and (item["prop_sprop_foundation"] ==
                     (["PropSPropFoundation.interpret_strict"] if status != "CERTIFIED" else [])),
                f"semantic/assumption gate failed: {name}")
    proof = (controlled / "GenericSchedulerCorrespondence.v").read_text()
    require(all(token in proof for token in
                ("gs_replace_at_correspondence", "gs_target_prefix_zero",
                 "gs_target_prefix_succ", "gs_prefix_correspondence",
                 "gs_pointwise_policy_application")),
            "operation-level proof dependency DAG missing")
    require(not output("git", "-C", str(ROOT), "status", "--porcelain", "--",
                       "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = VALIDATION / "imported/translation_order/generic_scheduler"
    manifest_path = PIPE / "implementation_definitions_generic_scheduler_module_manifest.json"
    status_path = PIPE / "implementation_definitions_generic_scheduler_module_status.json"
    require(not destination.exists() and not manifest_path.exists()
            and not status_path.exists(), "already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    staged = Path(tempfile.mkdtemp(prefix=".generic-scheduler-", dir=destination.parent))
    evidence = {
        "source_vo": source_vo, "production_olean": olean,
        "lean_type_guard_olean": lean_guard_olean, "source_type_guard_vo": source_guard_vo,
        "export": exported, "imported_v": imported_v, "imported_vo": imported_vo,
        "assumption_summary": WORK / "assumption_audit.json",
        "assumption_log": WORK / "GenericSchedulerAssumptionAudit.log",
        "lean_axiom_audit_log": lean_audit,
    }
    for key, path in list(evidence.items()):
        target = staged / (key + path.suffix)
        shutil.copy2(path, target)
        require(sha(target) == sha(path), f"publication copy corrupted: {key}")
        evidence[key] = target
    (staged / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            original = cert_dir / (name + suffix)
            target = staged / "certificates" / original.name
            shutil.copy2(original, target)
            require(sha(target) == sha(original), f"certificate copy corrupted: {name}")
            evidence[name + suffix] = target
    staged.rename(destination)
    evidence = {key: destination / path.relative_to(staged)
                for key, path in evidence.items()}
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        item = summary["certificates"][name]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Implementation.Definitions.GenericScheduler." + name,
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_fingerprint": row["final_type_or_type_fingerprint"],
            "semantic_certificate": item["certificate"],
            "semantic_status": item["status"],
            "semantic_premises": [], "statement_only_dependencies": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation": item["prop_sprop_foundation"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": "IMPLEMENTATION_DEFINITIONS_GENERIC_SCHEDULER",
        "source_commit": PIN, "source_file": SOURCE, "source_file_sha256": SOURCE_SHA,
        "direct_file_dependencies": sorted(deps),
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "validation_mode": "FILE_VALIDATE_WITH_VERIFIED_ACCEPTED_PRODUCERS",
        "target_build": "FRESH", "export": "FRESH", "rocq_import": "FRESH",
        "acceptance": "ACCEPTED_V06_FILE", "declarations": declarations,
        "artifact_hashes": {key + "_sha256": sha(path) for key, path in evidence.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT)) for key, path in evidence.items()},
        "export_config_sha256": sha(config),
        "tooling_manifest_sha256": sha(VALIDATION / "tooling/tooling_manifest.json"),
        "previous_status_file": previous_path.name,
        "previous_status_sha256": sha(previous_path),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = {**previous["coverage"],
                "accepted_files": previous["coverage"]["accepted_files"] + 1,
                "accepted_declarations": previous["coverage"]["accepted_declarations"] + 4}
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 4, "translated": 4, "proof_clean": 4,
            "certified": 2, "certified_with_prop_sprop_foundation": 2,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": coverage, "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "coverage": coverage}, sort_keys=True))


if __name__ == "__main__":
    main()
