#!/usr/bin/env python3
"""Fail-closed publication of model/task/jitter.v (Rank 77).

Consumes the fresh run produced by validate_model_task_jitter.sh.
"""

from __future__ import annotations

import csv
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
V = PROJECT / "Validation"
WORK = V / ".work/experiments/model_task_jitter_final"
PIPE = V / "planning/v06_pipeline"
CERT = V / "certificates/model_task_jitter"
FIXTURES = V / "fixtures/translation_order"
SOURCE = "model/task/jitter.v"
PRODUCTION = "Prosa/Model/Task/Jitter.lean"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
DEPENDENCIES = {"model/readiness/jitter.v", "model/task/concept.v"}
TARGETS = ["TaskJitter", "valid_jitter", "valid_jitter_bounds"]
LEAN_NS = "Prosa.Model.Task.Jitter."
PRINCIPAL = {"TaskJitter": ["TaskJitter_source_total", "TaskJitter_target_total",
                            "TaskJitter_source_roundtrip"]}
CERT_MODULES = ["TaskJitterBaseAdapter", "TaskJitterCorrespondence", "TaskJitterAssumptionAudit"]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("TASKJITTER_PUBLICATION_REJECTED: " + message)


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
    """Return the status file that records source_file as accepted."""
    for path in sorted(PIPE.glob("*status.json")):
        item = read(path).get("per_file", {}).get(source_file)
        if isinstance(item, dict) and item.get("status") == "ACCEPTED_V06_FILE":
            return path.name
    raise SystemExit(f"TASKJITTER_PUBLICATION_REJECTED: dependency not accepted: {source_file}")


def main() -> None:
    source_root = V / ".work/prosa-v06-414e667"
    official = source_root / SOURCE
    copied = WORK / "source" / SOURCE
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
    concept = read(PIPE / "model_task_concept_module_manifest.json")
    require(concept["acceptance"] == "ACCEPTED_V06_FILE"
            and sha(PROJECT / concept["production_file"]) == concept["production_source_sha256"]
            and sha(WORK / "olean/Prosa/Model/Task/Concept.olean")
            == concept["production_olean_sha256"],
            "accepted concept dependency changed")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream) if row["source_file"] == SOURCE]
    require([row["declaration_name"] for row in rows] == TARGETS,
            "authoritative declaration inventory changed")
    type_evidence = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        item = type_evidence[row["qualified_name"]]
        require(row["final_type_or_type_fingerprint"] == "rocq-check-sha256:" + item["sha256"],
                f"source type evidence changed for {row['declaration_name']}")

    # Source binding: pinned task/jitter.v compiled byte-identical on the
    # accepted concept source closure.
    require(sha(source_root / SOURCE) == sha(WORK / "source" / SOURCE)
            and sha(source_root / "util/nat.v") == sha(WORK / "source/util/nat.v"),
            "source copy is not byte-identical to pinned source")
    with tempfile.TemporaryDirectory(prefix="taskjitter-source-") as folder:
        for relative, patch in (("util/tactics.v", "prosa-v06-rocq93-util-tactics.patch"),
                                ("model/readiness/jitter.v", "prosa-v06-rocq93-model-readiness-jitter.patch")):
            target = Path(folder) / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_root / relative, target)
            subprocess.run(["patch", "-s", "-p1", "-d", folder, "-i", str(V / "patches" / patch)], check=True)
            require(sha(target) == sha(WORK / "source" / relative), f"patched dependency mismatch: {relative}")
    rjitter = read(PIPE / "model_readiness_jitter_module_manifest.json")
    require(rjitter["acceptance"] == "ACCEPTED_V06_FILE"
            and sha(WORK / "olean/Prosa/Model/Readiness/Jitter.olean") == rjitter["production_olean_sha256"],
            "accepted readiness/jitter dependency changed")
    fingerprint_log = (WORK / "source_type_fingerprint.log").read_text()
    found = {m.group(1): hashlib.sha256(" ".join(m.group(2).strip().split()).encode()).hexdigest()
             for m in re.finditer(r"(?ms)^BEGIN\|([^\n]+)\n(.*?)^END\|\1\s*$", fingerprint_log)}
    require(len(found) == len(TARGETS)
            and all(found.get(r["qualified_name"]) == type_evidence[r["qualified_name"]]["sha256"]
                    for r in rows),
            "elaborated source types do not match the authoritative fingerprints")
    source_vo = copied.with_suffix(".vo")
    require(sha(source_vo) and source_vo.stat().st_mtime_ns > copied.stat().st_mtime_ns,
            "official source .vo missing or stale")
    source_audit = fingerprint_log
    require("Error" not in source_audit
            and all(n in source_audit for n in TARGETS),
            "Rocq source type audit failed")

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
    target_olean = WORK / "olean/Prosa/Model/Task/Jitter.olean"
    require(sha(production) and sha(target_olean)
            and target_olean.stat().st_mtime_ns > production.stat().st_mtime_ns,
            "target .olean missing or stale")
    require(not re.search(r"\b(sorry|admit|axiom|unsafe)\b", production.read_text(), re.I),
            "forbidden Lean escape in production source")
    lean_log = (WORK / "lean_type_audit.log").read_text()
    require("error" not in lean_log.lower() and "sorryAx" not in lean_log
            and all(LEAN_NS + n in lean_log for n in TARGETS),
            "Lean type audit failed")
    lean_axioms = read(WORK / "lean_axiom_summary.json")
    require(not lean_axioms["missing"] and not lean_axioms["extra"]
            and set(lean_axioms["declarations"]) == {LEAN_NS + n for n in TARGETS}
            and all(item["status"] == "PASS" and not item["unexpected_axioms"]
                    for item in lean_axioms["declarations"].values()),
            "Lean axiom audit failed")

    export_config = V / "tooling/model_task_jitter_export_config.json"
    exported = WORK / "imported/TaskJitter.out"
    imported_wrapper = WORK / "imported/ImportedTaskJitter.v"
    imported_vo = WORK / "imported/ImportedTaskJitter.vo"
    metadata = read(WORK / "export_metadata.json")
    config = read(export_config)
    require(metadata["module"] == "Prosa.Model.Task.Jitter"
            and metadata["statement_only_count"] == 0 and config["statement_only"] == []
            and all(LEAN_NS + n in config["targets"] for n in TARGETS)
            and metadata["config_sha256"] == sha(export_config)
            and metadata["output_sha256"] == sha(exported),
            "actual export metadata, configuration or kernel guards changed")
    require(imported_wrapper.read_text() ==
            'From LeanImport Require Import Lean.\nLean Import "TaskJitter.out".\n',
            "import wrapper changed")
    require(imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns, "imported .vo is stale")
    require(sha(WORK / "imported/Subadditivity.out")
            == sha(V / "imported/foundation_slice_2/Subadditivity.out"),
            "shared Nat artifact is not the accepted Subadditivity export")
    type_audit = (WORK / "imported_type_audit.log").read_text()
    require("Error" not in type_audit
            and all(f"Prosa_Model_Task_Jitter_{n}" in type_audit for n in TARGETS),
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

    summary = read(WORK / "assumption_summary.json")
    assumption_config = read(CERT / "task_jitter_assumption_config.json")
    require(summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(assumption_config["certificates"])
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

    previous_path = PIPE / "model_task_arrivals_module_status.json"
    previous = read(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 75
            and previous["coverage"]["accepted_declarations"] == 535,
            "formal baseline changed")
    arrivals = read(PIPE / "model_task_arrivals_module_status.json")
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
    manifest = {
        "slice": "TRANSLATION_ORDER_MODEL_TASK_JITTER",
        "generated_at": now.isoformat(),
        "published_at": now.isoformat(),
        "rank": 77,
        "layer": 11,
        "source_file": SOURCE,
        "source_commit": PIN,
        "source_tree": TREE,
        "source_file_sha256": sha(official),
        "source_compatibility": {"note": "pinned source compiled byte-identical",
                                 "elaborated_type_fingerprints_matched": len(TARGETS)},
        "dependency_source_patches": ["prosa-v06-rocq93-util-tactics.patch",
                                      "prosa-v06-rocq93-model-readiness-jitter.patch"],
        "file_dependencies": dependency_evidence,
        "production_file": PRODUCTION,
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(target_olean),
        "export_config_sha256": sha(export_config),
        "export_sha256": sha(exported),
        "export_lines": sum(1 for _ in exported.open("rb")),
        "export_bytes": exported.stat().st_size,
        "import_sha256": sha(imported_vo),
        "source_vo_sha256": sha(source_vo),
        "lean_axiom_summary_sha256": sha(WORK / "lean_axiom_summary.json"),
        "rocq_assumption_summary_sha256": sha(WORK / "assumption_summary.json"),
        "assumption_config_sha256": sha(CERT / "task_jitter_assumption_config.json"),
        "stage_timing_seconds": {stage: {"mode": mode, "seconds": int(sec)}
                                 for stage, mode, sec in timing},
        "certificates": {name: {"source_sha256": sha(CERT / f"{name}.v"),
                                "vo_sha256": sha(WORK / f"certificates/{name}.vo")}
                         for name in CERT_MODULES},
        "declarations": declarations,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = PIPE / "model_task_jitter_module_manifest.json"
    status_path = PIPE / "model_task_jitter_module_status.json"
    require(not manifest_path.exists()
            and (not status_path.exists() or read(status_path)["status"] != "PASS"),
            "task jitter publication already exists")
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": manifest["slice"],
        "status": "PASS",
        "source_file": SOURCE,
        "per_file": {SOURCE: {
            "public_declarations": 3,
            "translated": 3,
            "proof_clean": 3,
            "semantic_proof_compiled": 3,
            "certified": 3,
            "status": "ACCEPTED_V06_FILE",
            "published_at": now.isoformat(),
        }},
        "coverage": {
            "accepted_files": 76,
            "authoritative_files": 357,
            "accepted_declarations": 538,
            "authoritative_declarations": 2439,
            "translated_but_not_certified":
                previous["coverage"]["translated_but_not_certified"],
            "deferred_external_boundary": previous["coverage"]["deferred_external_boundary"],
        },
        "previous_status_sha256": sha(previous_path),
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2) + "\n")

    destination = V / "imported/translation_order/model_task_jitter"
    require(not destination.exists(), "publication destination already exists")
    (destination / "certificates").mkdir(parents=True)
    for path in (exported, imported_wrapper, imported_vo, WORK / "export_metadata.json",
                 WORK / "lean_type_audit.log", WORK / "lean_axiom_summary.json",
                 WORK / "assumption_summary.json", WORK / "source_type_fingerprint.log",
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
