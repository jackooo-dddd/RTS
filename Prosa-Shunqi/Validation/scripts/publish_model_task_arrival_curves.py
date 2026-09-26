#!/usr/bin/env python3
"""Fail-closed publication of model/task/arrival/curves.v (Rank 85).

Consumes the fresh run produced by validate_model_task_arrival_curves.sh.
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
WORK = V / ".work/experiments/model_task_arrival_curves_final"
PIPE = V / "planning/v06_pipeline"
CERT = V / "certificates/model_task_arrival_curves"
SOURCE = "model/task/arrival/curves.v"
PRODUCTION = "Prosa/Model/Task/Arrival/Curves.lean"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
DEPENDENCIES = {"model/task/arrivals.v", "util/rel.v"}
LEAN_NS = "Prosa.Model.Task.Arrival.Curves."
CLASSES = ["MaxArrivals", "MinArrivals", "MinSeparation", "MaxSeparation"]
COMPUTATIONAL = set(CLASSES) | {"valid_arrival_curve", "respects_max_arrivals",
    "respects_min_arrivals", "respects_min_separation", "respects_max_separation",
    "valid_taskset_arrival_curve", "taskset_respects_max_arrivals",
    "taskset_respects_min_arrivals", "taskset_respects_max_separation",
    "taskset_respects_min_separation"}
PRINCIPAL = {c: [c + "_source_total", c + "_target_total"] for c in CLASSES}
CERT_MODULES = [
    "ArrivalsSeqBaseAdapter", "ArrivalsSeqOperations", "ArrivalsSeqCorrespondence",
    "ArrivalsCorrespondence", "CurvesCorrespondence", "CurvesAssumptionAudit",
]
HELPERS = ["cv_import_fun_rel", "cv_export_fun_rel", "cv_family_import", "cv_family_export"]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("CURVES_PUBLICATION_REJECTED: " + message)


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
    raise SystemExit(f"CURVES_PUBLICATION_REJECTED: dependency not accepted: {source_file}")


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
    require(len(targets) == 14, "authoritative declaration inventory changed")
    type_evidence = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        item = type_evidence[row["qualified_name"]]
        require(row["final_type_or_type_fingerprint"] == "rocq-check-sha256:" + item["sha256"],
                f"source type evidence changed for {row['declaration_name']}")

    # Source binding: pinned rel.v and curves.v compiled byte-identically on
    # the accepted model/task/arrivals source closure.
    copied = WORK / "source" / SOURCE
    require(sha(copied) == sha(official), "compiled source copy is not byte-identical")
    require(sha(WORK / "source/util/rel.v") == sha(source_root / "util/rel.v"),
            "util/rel.v copy is not byte-identical")
    source_vo = copied.with_suffix(".vo")
    require(sha(source_vo) and source_vo.stat().st_mtime_ns > copied.stat().st_mtime_ns,
            "official source .vo missing or stale")
    require("Error" not in (WORK / "source_build.log").read_text(), "source build failed")
    arr = read(PIPE / "model_task_arrivals_module_manifest.json")
    require(arr["acceptance"] == "ACCEPTED_V06_FILE"
            and sha(WORK / "source/model/task/arrivals.vo") == arr["source_vo_sha256"]
            and sha(WORK / "olean/Prosa/Model/Task/Arrivals.olean")
            == arr["production_olean_sha256"],
            "accepted model/task/arrivals dependency changed")
    fingerprint_log = (WORK / "source_type_fingerprint.log").read_text()
    require("Error" not in fingerprint_log, "Rocq source type audit failed")
    blocks = {m.group(1): " ".join(m.group(2).split())
              for m in re.finditer(r"(?ms)^BEGIN\|([^\n]+)\n(.*?)^END\|\1\s*$", fingerprint_log)}
    fingerprint_matches = {}
    for row in rows:
        name = row["qualified_name"]
        got = blocks.get(name)
        require(got is not None
                and hashlib.sha256(got.encode()).hexdigest() == type_evidence[name]["sha256"],
                f"source fingerprint mismatch: {name}")
        fingerprint_matches[name] = "EXACT_HASH"

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
    target_olean = WORK / "olean/Prosa/Model/Task/Arrival/Curves.olean"
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

    export_config = V / "tooling/model_task_arrival_curves_export_config.json"
    exported = WORK / "imported/Curves.out"
    imported_wrapper = WORK / "imported/ImportedCurves.v"
    imported_vo = WORK / "imported/ImportedCurves.vo"
    metadata = read(WORK / "export_metadata.json")
    config = read(export_config)
    expected_statement_only = [LEAN_NS + n for n in targets if n not in COMPUTATIONAL]
    require(metadata["module"] == "Validation.fixtures.translation_order.CurvesComputationInterface"
            and config["statement_only"] == expected_statement_only
            and metadata["statement_only_count"] == 0
            and all(LEAN_NS + n in config["targets"] for n in targets)
            and all(LEAN_NS + n in config["definition_targets"] for n in COMPUTATIONAL - set(CLASSES))
            and config["statement_only"] == []
            and metadata["config_sha256"] == sha(export_config)
            and metadata["output_sha256"] == sha(exported),
            "actual export metadata, configuration or kernel guards changed")
    require(imported_wrapper.read_text() ==
            'From LeanImport Require Import Lean.\nLean Import "Curves.out".\n',
            "import wrapper changed")
    require(imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns, "imported .vo is stale")
    require(sha(WORK / "imported/Subadditivity.out")
            == sha(V / "imported/foundation_slice_2/Subadditivity.out"),
            "shared Nat artifact is not the accepted Subadditivity export")
    type_audit = (WORK / "imported_type_audit.log").read_text()
    require("Error" not in type_audit
            and all(f"Prosa_Model_Task_Arrival_Curves_{n}" in type_audit for n in targets),
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
    cert_text = (CERT / "CurvesCorrespondence.v").read_text()
    require(not re.search(r"\b(Admitted|admit|Axiom|Parameter)\b", cert_text),
            "certificate escape")

    summary = read(WORK / "assumption_summary.json")
    assumption_config = read(CERT / "curves_assumption_config.json")
    require(summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(assumption_config["certificates"])
            == {c for n in targets for c in PRINCIPAL.get(n, [f"{n}_correspondence"])} | set(HELPERS)
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

    previous_path = PIPE / "model_priority_coercion_module_status.json"
    previous = read(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 83
            and previous["coverage"]["accepted_declarations"] == 608,
            "formal baseline changed")
    require(not git(ROOT, "status", "--porcelain", "--", "Prosa-fei"),
            "historical Prosa-fei workspace changed")

    now = datetime.now(timezone.utc).astimezone()
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        certs = PRINCIPAL.get(name, [f"{name}_correspondence"])
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
        "slice": "TRANSLATION_ORDER_MODEL_TASK_ARRIVAL_CURVES",
        "generated_at": now.isoformat(),
        "published_at": now.isoformat(),
        "rank": 85,
        "layer": 12,
        "source_file": SOURCE,
        "source_commit": PIN,
        "source_tree": TREE,
        "source_file_sha256": sha(official),
        "source_compatibility": {"note": "pinned source compiled byte-identical",
                                 "elaborated_type_fingerprints_matched": len(targets)},
        "source_type_evidence": fingerprint_matches,
        "statement_only_export_boundary": expected_statement_only,
        "lean_representation_note": ("singleton classes as one-field Lean classes; "
            "`monotone leq` as `monotone (fun x y => decide (x <= y))`; "
            "`tsk \\in ts` as `decide (tsk ∈ ts) = true`"),
        "input_relations": ["Lean.eq on the JobTask job_task field",
                            "ArArrivalSequenceRel", "ArListRel (task sets)",
                            "SubNatFunRel / CvCurveFamilyRel (curves, class instances)"],
        "coverage_for_inner_binders": ["instants (Nat, both directions)",
                                       "tasks (identity carrier)"],
        "input_relation_totality": ["curves: cv_import_fun_rel / cv_export_fun_rel",
                                    "classes: <Class>_source_total / <Class>_target_total"],
        "export_lines_note": "within the 50k soft budget",
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
        "assumption_config_sha256": sha(CERT / "curves_assumption_config.json"),
        "stage_timing_seconds": {stage: {"mode": mode, "seconds": int(sec)}
                                 for stage, mode, sec in timing},
        "certificates": {name: {"source_sha256": sha(CERT / f"{name}.v"),
                                "vo_sha256": sha(WORK / f"certificates/{name}.vo")}
                         for name in CERT_MODULES},
        "declarations": declarations,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = PIPE / "model_task_arrival_curves_module_manifest.json"
    status_path = PIPE / "model_task_arrival_curves_module_status.json"
    require(not manifest_path.exists()
            and (not status_path.exists() or read(status_path)["status"] != "PASS"),
            "publication already exists")
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": manifest["slice"],
        "status": "PASS",
        "source_file": SOURCE,
        "per_file": {SOURCE: {
            "public_declarations": 14,
            "translated": 14,
            "proof_clean": 14,
            "semantic_proof_compiled": 14,
            "certified": 14,
            "status": "ACCEPTED_V06_FILE",
            "published_at": now.isoformat(),
        }},
        "coverage": {
            "accepted_files": 84,
            "authoritative_files": 357,
            "accepted_declarations": 622,
            "authoritative_declarations": 2439,
            "translated_but_not_certified":
                previous["coverage"]["translated_but_not_certified"],
            "deferred_external_boundary": previous["coverage"]["deferred_external_boundary"],
        },
        "previous_status_sha256": sha(previous_path),
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2) + "\n")

    destination = V / "imported/translation_order/model_task_arrival_curves"
    require(not destination.exists(), "publication destination already exists")
    (destination / "certificates").mkdir(parents=True)
    for path in (exported, imported_wrapper, imported_vo, WORK / "export_metadata.json",
                 WORK / "lean_type_audit.log", WORK / "lean_axiom_summary.json",
                 WORK / "assumption_summary.json", WORK / "source_type_fingerprint.log",
                 WORK / "source_build.log",
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
