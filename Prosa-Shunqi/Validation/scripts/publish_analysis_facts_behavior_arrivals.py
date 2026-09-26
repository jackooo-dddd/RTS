#!/usr/bin/env python3
"""Fail-closed publication of analysis/facts/behavior/arrivals.v (Rank 82).

Consumes the fresh run produced by validate_analysis_facts_behavior_arrivals.sh.
"""

from __future__ import annotations

import csv
import hashlib
import json
import re
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
V = PROJECT / "Validation"
WORK = V / ".work/experiments/analysis_facts_behavior_arrivals_final"
PIPE = V / "planning/v06_pipeline"
CERT = V / "certificates/analysis_facts_behavior_arrivals"
SOURCE = "analysis/facts/behavior/arrivals.v"
PRODUCTION = "Prosa/Analysis/Facts/Behavior/Arrivals.lean"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
DEPENDENCIES = {"behavior/all.v", "model/task/arrivals.v", "util/all.v"}
LEAN_NS = "Prosa.Analysis.Facts.Behavior.Arrivals."
COMPUTATIONAL = {"by_arrival_times"}
CERT_MODULES = [
    "ArrivalsSeqBaseAdapter", "ArrivalsSeqOperations", "ArrivalsSeqCorrespondence",
    "ArrivalsCorrespondence", "JitterSvcBaseAdapter", "JitterSvcNatBoolOperations",
    "JitterSvcIntervalOperations", "JitterSvcScheduleOperations", "JitterSvcJobOperations",
    "FactsArrivalsCorrespondence", "FactsArrivalsAssumptionAudit",
]
HELPERS = ["fa_forall_arrival_sequence", "fa_forall_pred", "fa_forall_list", "fa_forall_schedule",
           "fa_sched_to_target_rel", "fa_sched_to_source_rel", "fa_sorted_ischain",
           "fa_bigcat_related", "fa_jobs_come_from_related", "fa_jobs_must_arrive_related",
           "fa_pending_related", "fa_backlogged_related", "fa_valid_schedule_related",
           "fa_all_jobs_from_taskset_related"]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("FARRIVALS_PUBLICATION_REJECTED: " + message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def output(*args: str) -> str:
    return subprocess.check_output(args, text=True, cwd=PROJECT).strip()


def git(source: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(source), *args], text=True).strip()


def accepted_file(source_file: str) -> str:
    for path in sorted(PIPE.glob("*status.json")):
        item = read(path).get("per_file", {}).get(source_file)
        if isinstance(item, dict) and item.get("status") == "ACCEPTED_V06_FILE":
            return path.name
    raise SystemExit(f"FARRIVALS_PUBLICATION_REJECTED: dependency not accepted: {source_file}")


def main() -> None:
    source_root = V / ".work/prosa-v06-414e667"
    official = source_root / SOURCE
    require(git(source_root, "rev-parse", "HEAD") == PIN, "source commit changed")
    require(git(source_root, "rev-parse", "HEAD^{tree}") == TREE, "source tree changed")
    require(not git(source_root, "status", "--porcelain", "--untracked-files=all"),
            "pinned source worktree is dirty")

    with (V / "planning/v06_dependency/file_inventory.csv").open() as stream:
        file_row = next(r for r in csv.DictReader(stream) if r["file"] == SOURCE)
    require(file_row["sha256"] == sha(official), "authoritative file inventory mismatch")
    dag = read(V / "planning/v06_dependency/file_dag.json")
    deps = {e["dependency_file"] for e in dag["edges"] if e["dependent_file"] == SOURCE}
    require(deps == DEPENDENCIES, f"authoritative file DAG changed: {sorted(deps)}")
    dependency_evidence = {dep: accepted_file(dep) for dep in sorted(deps)}
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream) if row["source_file"] == SOURCE]
    targets = [row["declaration_name"] for row in rows]
    require(len(targets) == 45, "authoritative declaration inventory changed")
    type_evidence = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        item = type_evidence[row["qualified_name"]]
        require(row["final_type_or_type_fingerprint"] == "rocq-check-sha256:" + item["sha256"],
                f"source type evidence changed for {row['declaration_name']}")

    # Source binding: proof-independent semantic extraction of the pinned file.
    extraction = read(WORK / "source_extraction.json")
    extracted = WORK / "source/FactsArrivalsSemanticSource.v"
    extracted_text = extracted.read_text()
    require(extraction["source_file_sha256"] == sha(official)
            and extraction["source_commit"] == PIN
            and extraction["mode"] == "proof_independent_semantic_source_signature",
            "semantic extraction is not bound to the pinned source")
    require(not re.search(r"\b(Admitted|Axiom|Parameter|admit)\b", extracted_text),
            "extracted source contains an escape")
    require(set(extraction["declarations"]) == set(targets), "extraction declaration set changed")
    for name, item in extraction["declarations"].items():
        if name in COMPUTATIONAL:
            require(item["acquisition_mode"] == "BODY_EXACT"
                    and item["generated_text_sha256"] == item["source_block_sha256"],
                    f"computational body not byte-identical: {name}")
        else:
            require(item["acquisition_mode"] == "STATEMENT_EXACT_PROOF_OMITTED"
                    and item["statement_sort"] == "Prop",
                    f"statement extraction mode changed: {name}")
    fingerprint_log = (WORK / "source_type_fingerprint.log").read_text()
    require("Error" not in fingerprint_log, "Rocq source type audit failed")
    blocks = {m.group(1): " ".join(m.group(2).split())
              for m in re.finditer(r"(?ms)^BEGIN\|([^\n]+)\n(.*?)^END\|\1\s*$", fingerprint_log)}
    fingerprint_matches = {}
    for row in rows:
        name = row["qualified_name"]
        got = blocks.get(name)
        require(got is not None, f"missing source fingerprint: {name}")
        want = type_evidence[name]["normalized_check"]
        if hashlib.sha256(got.encode()).hexdigest() == type_evidence[name]["sha256"]:
            fingerprint_matches[name] = "EXACT_HASH"
            continue
        m = re.match(r"statement_\S+ = (.*) : Prop$", got)
        fingerprint_matches[name] = ("STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE"
            if m and m.group(1) == want.split(" : ", 1)[1] else "MISMATCH")
    require("MISMATCH" not in fingerprint_matches.values(),
            "elaborated source types do not match the authoritative evidence")
    source_vo = extracted.with_suffix(".vo")
    require(sha(source_vo) and source_vo.stat().st_mtime_ns > extracted.stat().st_mtime_ns,
            "semantic source .vo missing or stale")
    arrivals_manifest = read(PIPE / "model_task_arrivals_module_manifest.json")
    require(sha(WORK / "source/model/task/arrivals.vo") == arrivals_manifest["source_vo_sha256"],
            "model/task/arrivals source closure changed")
    for stem, olean in (("model_task_arrivals", "Prosa/Model/Task/Arrivals.olean"),
                        ("model_task_concept", "Prosa/Model/Task/Concept.olean")):
        dep = read(PIPE / f"{stem}_module_manifest.json")
        require(dep["acceptance"] == "ACCEPTED_V06_FILE"
                and sha(WORK / "olean" / olean) == dep["production_olean_sha256"],
                f"accepted dependency changed: {stem}")

    require("Lean (version 4.33.1" in output("lake", "env", "lean", "--version")
            and git(PROJECT / ".lake/packages/mathlib", "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in output("opam", "exec", "--switch=rocq93rc1", "--", "rocq", "--version"),
            "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    require(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / PRODUCTION
    target_olean = WORK / "olean/Prosa/Analysis/Facts/Behavior/Arrivals.olean"
    require(sha(production) and sha(target_olean)
            and target_olean.stat().st_mtime_ns > production.stat().st_mtime_ns,
            "target .olean missing or stale")
    require(not re.search(r"\b(sorry|admit|axiom|unsafe)\b", production.read_text(), re.I),
            "forbidden Lean escape in production source")
    lean_log = (WORK / "lean_type_audit.log").read_text()
    require("error" not in lean_log.lower() and "sorryAx" not in lean_log
            and all(LEAN_NS + n in lean_log for n in targets),
            "Lean type audit failed")
    lean_axioms = read(WORK / "lean_axiom_summary.json")
    require(not lean_axioms["missing"] and not lean_axioms["extra"]
            and set(lean_axioms["declarations"]) == {LEAN_NS + n for n in targets}
            and all(item["status"] == "PASS" and not item["unexpected_axioms"]
                    for item in lean_axioms["declarations"].values()),
            "Lean axiom audit failed")

    export_config = V / "tooling/analysis_facts_behavior_arrivals_export_config.json"
    exported = WORK / "imported/FactsArrivals.out"
    imported_wrapper = WORK / "imported/ImportedFactsArrivals.v"
    imported_vo = WORK / "imported/ImportedFactsArrivals.vo"
    metadata = read(WORK / "export_metadata.json")
    config = read(export_config)
    expected_statement_only = [LEAN_NS + n for n in targets if n not in COMPUTATIONAL]
    require(metadata["module"] == "Validation.fixtures.translation_order.FactsArrivalsComputationInterface"
            and config["statement_only"] == expected_statement_only
            and metadata["statement_only_count"] == len(expected_statement_only)
            and all(LEAN_NS + n in config["targets"] for n in targets)
            and LEAN_NS + "by_arrival_times" in config["definition_targets"]
            and metadata["config_sha256"] == sha(export_config)
            and metadata["output_sha256"] == sha(exported),
            "actual export metadata, configuration or kernel guards changed")
    require(imported_wrapper.read_text() ==
            'From LeanImport Require Import Lean.\nLean Import "FactsArrivals.out".\n',
            "import wrapper changed")
    require(imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns, "imported .vo is stale")
    require(sha(WORK / "imported/Subadditivity.out")
            == sha(V / "imported/foundation_slice_2/Subadditivity.out"),
            "shared Nat artifact is not the accepted Subadditivity export")
    type_audit = (WORK / "imported_type_audit.log").read_text()
    require("Error" not in type_audit
            and all(f"Prosa_Analysis_Facts_Behavior_Arrivals_{n}" in type_audit for n in targets),
            "imported exact-type audit failed")

    for name in CERT_MODULES:
        require(sha(CERT / f"{name}.v") == sha(WORK / f"certificates/{name}.v"),
                f"compiled certificate differs from canonical source: {name}")
        vo = WORK / f"certificates/{name}.vo"
        require(sha(vo) and "Error" not in (WORK / f"certificates/{name}.log").read_text(),
                f"certificate compile failed: {name}")
    for name in ("PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence"):
        require(sha(V / f"certificates/common/{name}.v") == sha(WORK / f"certificates/{name}.v"),
                f"common certificate differs: {name}")
    cert_text = (CERT / "FactsArrivalsCorrespondence.v").read_text()
    require(not re.search(r"\b(Admitted|admit|Axiom|Parameter)\b", cert_text),
            "certificate escape")

    summary = read(WORK / "assumption_summary.json")
    assumption_config = read(CERT / "facts_arrivals_assumption_config.json")
    require(summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(assumption_config["certificates"])
            == {f"{n}_correspondence" for n in targets} | set(HELPERS)
            and assumption_config["statement_only_dependencies"] == [],
            "Rocq assumption summary is incomplete")
    allowed = {"CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
    for item in summary["certificates"].values():
        require(item["status"] in allowed and not item["semantic_premises"]
                and not item["statement_only_dependencies"]
                and not item["unexpected"]
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"],
                "Rocq semantic gate failed")

    previous_path = PIPE / "analysis_facts_sbf_module_status.json"
    previous = read(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 80
            and previous["coverage"]["accepted_declarations"] == 547,
            "formal baseline changed")
    require(not git(ROOT, "status", "--porcelain", "--", "Prosa-fei"),
            "historical Prosa-fei workspace changed")

    now = datetime.now(timezone.utc).astimezone()
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        certs = [f"{name}_correspondence"]
        statuses = {summary["certificates"][c]["status"] for c in certs}
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": LEAN_NS + name,
            "semantic_status": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                if "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" in statuses else "CERTIFIED",
            "certificates": certs,
            "semantic_premises": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    timing = [line.split("\t") for line in (WORK / "stage_timing.tsv").read_text().splitlines()]
    export_lines = sum(1 for _ in exported.open("rb"))
    manifest = {
        "slice": "TRANSLATION_ORDER_ANALYSIS_FACTS_BEHAVIOR_ARRIVALS",
        "generated_at": now.isoformat(),
        "published_at": now.isoformat(),
        "rank": 82,
        "layer": 12,
        "source_file": SOURCE,
        "source_commit": PIN,
        "source_tree": TREE,
        "source_file_sha256": sha(official),
        "source_compatibility": {
            "method": "extract_v06_semantic_source.py proof-independent semantic module",
            "note": "theorem statements exact (proofs omitted), by_arrival_times body byte-identical",
            "extracted_sha256": sha(extracted),
            "extraction_metadata_sha256": sha(WORK / "source_extraction.json"),
            "elaborated_type_fingerprints_matched": len(targets)},
        "source_type_evidence": fingerprint_matches,
        "statement_only_export_boundary": expected_statement_only,
        "input_relations": [
            "ArJobArrivalRel / SvcJobCostRel (job_arrival / job_cost fields)",
            "SvcProcessorStateRel + SvcScheduleRel (two-sided) for leading PState/sched binders",
            "FaJobReadyRel (job_ready data field over all related schedules; law field unused)",
            "Lean.eq on the JobTask job_task field"],
        "coverage_for_inner_binders": ["arrival sequences (both directions)",
                                       "schedules (Svc state import/export)",
                                       "predicates P (bool functions)",
                                       "task lists ts (both directions)"],
        "export_size_diagnosis": {
            "export_lines": export_lines,
            "soft_budget_flag": "OVER_100K_DIAGNOSED",
            "diagnosis": "the accepted Service/Schedule interface closure (Fintype core "
                         "enumeration, service_in list sum) alone is ~120k lines "
                         "(readiness/basic 120,236; TDMA 120,859); this file adds ~6.9k "
                         "lines; import took 46 s"},
        "file_dependencies": dependency_evidence,
        "production_file": PRODUCTION,
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(target_olean),
        "export_config_sha256": sha(export_config),
        "export_sha256": sha(exported),
        "export_lines": export_lines,
        "export_bytes": exported.stat().st_size,
        "import_sha256": sha(imported_vo),
        "source_vo_sha256": sha(source_vo),
        "lean_axiom_summary_sha256": sha(WORK / "lean_axiom_summary.json"),
        "rocq_assumption_summary_sha256": sha(WORK / "assumption_summary.json"),
        "assumption_config_sha256": sha(CERT / "facts_arrivals_assumption_config.json"),
        "stage_timing_seconds": {stage: {"mode": mode, "seconds": int(sec)}
                                 for stage, mode, sec in timing},
        "certificates": {name: {"source_sha256": sha(CERT / f"{name}.v"),
                                "vo_sha256": sha(WORK / f"certificates/{name}.vo")}
                         for name in CERT_MODULES},
        "declarations": declarations,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = PIPE / "analysis_facts_behavior_arrivals_module_manifest.json"
    status_path = PIPE / "analysis_facts_behavior_arrivals_module_status.json"
    require(not manifest_path.exists()
            and (not status_path.exists() or read(status_path)["status"] != "PASS"),
            "publication already exists")
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": manifest["slice"],
        "status": "PASS",
        "source_file": SOURCE,
        "per_file": {SOURCE: {
            "public_declarations": 45,
            "translated": 45,
            "proof_clean": 45,
            "semantic_proof_compiled": 45,
            "certified": 45,
            "status": "ACCEPTED_V06_FILE",
            "published_at": now.isoformat(),
        }},
        "coverage": {
            "accepted_files": 81,
            "authoritative_files": 357,
            "accepted_declarations": 592,
            "authoritative_declarations": 2439,
            "translated_but_not_certified":
                previous["coverage"]["translated_but_not_certified"],
            "deferred_external_boundary": previous["coverage"]["deferred_external_boundary"],
        },
        "previous_status_sha256": sha(previous_path),
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2) + "\n")

    destination = V / "imported/translation_order/analysis_facts_behavior_arrivals"
    require(not destination.exists(), "publication destination already exists")
    (destination / "certificates").mkdir(parents=True)
    for path in (exported, imported_wrapper, imported_vo, WORK / "export_metadata.json",
                 WORK / "lean_type_audit.log", WORK / "lean_axiom_summary.json",
                 WORK / "assumption_summary.json", WORK / "source_type_fingerprint.log",
                 WORK / "source_extraction.json", extracted,
                 WORK / "stage_timing.tsv", WORK / "imported_type_audit.log"):
        shutil.copy2(path, destination / path.name)
    for name in CERT_MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(WORK / "certificates" / f"{name}{suffix}",
                         destination / "certificates" / f"{name}{suffix}")
    print(json.dumps({"manifest": str(manifest_path), "status": str(status_path),
                      "publication": str(destination), "coverage": status["coverage"]},
                     indent=2))


if __name__ == "__main__":
    main()
