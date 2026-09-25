#!/usr/bin/env python3
"""Fail-closed whole-file publication of pinned model/task/concept.v."""

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
V = PROJECT / "Validation"
W = V / ".work/experiments/model_task_concept"
PIPE = V / "planning/v06_pipeline"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE = "model/task/concept.v"
MODULES = (
    "ReadyArrivalBaseAdapter", "ConceptOperations",
    "ReadyArrivalCorrespondence", "ConceptClasses",
    "ConceptCorrespondence", "ConceptTypeAudit", "ConceptAssumptionAudit",
)
PAIRED = {"JobTask", "TaskDeadline", "TaskCost", "TaskMinCost", "TaskSet"}


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise SystemExit(f"CONCEPT_PUBLICATION_REJECTED: {reason}")


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def output(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    selection = read(PIPE / "model_task_concept_selection.json")
    previous = read(PIPE / "model_schedule_work_conserving_module_status.json")
    require(selection["source_commit"] == PIN and selection["source_file"] == SOURCE
            and selection["rank"] == 61 and selection["layer"] == 10
            and selection["direct_internal_dependencies"] ==
            ["behavior/all.v", "util/all.v"] and selection["file_dag_ready"]
            and selection["public_declaration_count"] == 19,
            "selection/DAG/readiness mismatch")
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 57
            and previous["coverage"]["accepted_declarations"] == 395,
            "previous formal cumulative state changed")
    pinned = V / ".work/prosa-v06-414e667"
    official = pinned / SOURCE
    source_copy = W / "source" / SOURCE
    require(output("git", "-C", str(pinned), "rev-parse", "HEAD") == PIN
            and output("git", "-C", str(pinned), "rev-parse", "HEAD^{tree}")
            == "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
            and not output("git", "-C", str(pinned), "status", "--porcelain",
                           "--untracked-files=all")
            and sha(official) == sha(source_copy) == selection["source_sha256"],
            "official source not pinned and byte-identical")
    source_vo = source_copy.with_suffix(".vo")
    require(sha(source_vo) and source_vo.stat().st_mtime_ns > source_copy.stat().st_mtime_ns,
            "source Rocq compile missing or stale")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    names = [r["declaration_name"] for r in rows]
    require(names == selection["targets_in_source_order"] and len(names) == 19,
            "source declaration inventory changed")
    type_evidence = read(V / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + type_evidence[row["qualified_name"]]["sha256"],
                f"elaborated source type fingerprint changed: {row['declaration_name']}")

    for module in ("behavior", "util"):
        dep = read(PIPE / f"{module}_all_module_manifest.json")
        dep_status = read(PIPE / f"{module}_all_module_status.json")
        upper = module.capitalize()
        require(dep["acceptance"] == "ACCEPTED_V06_FILE"
                and dep_status["status"] == "PASS"
                and sha(PROJECT / dep["production_file"]) == dep["production_source_sha256"]
                and sha(W / f"olean/Prosa/{upper}/All.olean")
                == dep["production_olean_sha256"],
                f"accepted dependency changed: {module}/all")
    require("Lean (version 4.33.1" in output("lake", "env", "lean", "--version")
            and output("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                       "rev-parse", "HEAD")
            == "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in output("opam", "exec", "--switch=rocq93rc1", "--",
                                "rocq", "--version"),
            "toolchain changed")
    tooling = read(V / "tooling/tooling_manifest.json")
    require(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Model/Task/Concept.lean"
    olean = W / "olean/Prosa/Model/Task/Concept.olean"
    require(sha(production) and sha(olean)
            and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
            and not re.search(r"\b(sorry|axiom|unsafe)\b", production.read_text()),
            "production source, fresh compile or proof-clean text invalid")
    lean_audit = W / "lean_type_audit.log"
    audit_text = lean_audit.read_text()
    require("error:" not in audit_text and "sorryAx" not in audit_text
            and all(f"{n} :" in audit_text or f"@{n} :" in audit_text
                    for n in names)
            and "'Prosa.Model.Task.Concept.same_task_sym' depends on axioms: [propext]"
            in audit_text
            and "'Prosa.Model.Task.Concept.diff_task' depends on axioms: [propext]"
            in audit_text,
            "Lean type or theorem proof-axiom audit changed")

    config_path = V / "tooling/model_task_concept_export_config.json"
    config = read(config_path)
    exported = W / "imported/TaskConcept.out"
    meta = read(W / "export_metadata.json")
    require(config["module"] ==
            "Validation.fixtures.translation_order.TaskConceptComputationInterface"
            and config["statement_only"] == []
            and not any(config["normalization"].values())
            and len(config["body_theorems"]) == 9
            and meta["config_sha256"] == sha(config_path)
            and meta["output_sha256"] == sha(exported)
            and meta["statement_only_count"] == 0
            and meta["body_theorem_count"] == 9,
            "actual compiled export/config changed")
    for name in ("Bigcat", "ArrivalSequence", "TaskConcept"):
        fixture = V / f"fixtures/translation_order/{name}ComputationInterface.lean"
        fixture_olean = W / f"olean/Validation/fixtures/translation_order/{name}ComputationInterface.olean"
        require(sha(fixture_olean)
                and fixture_olean.stat().st_mtime_ns > fixture.stat().st_mtime_ns,
                f"computation interface stale: {name}")
    wrapper = W / "imported/ImportedTaskConcept.v"
    imported_vo = W / "imported/ImportedTaskConcept.vo"
    require(wrapper.read_text() ==
            'From LeanImport Require Import Lean.\nLean Import "TaskConcept.out".\n'
            and sha(imported_vo)
            and imported_vo.stat().st_mtime_ns > wrapper.stat().st_mtime_ns
            and imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns,
            "actual exported Lean artifact not freshly imported")

    controlled = V / "certificates/model_task_concept"
    compiled = W / "certificates"
    generated = read(compiled / "concept_arrival_instantiation.json")
    require(generated["imported_artifact_sha256"] == sha(imported_vo),
            "artifact-local adapter replay not bound to current import")
    require(generated["concept_base_adapter"]["output_sha256"] ==
            sha(compiled / "ReadyArrivalBaseAdapter.v"),
            "replayed base adapter changed")
    for name in MODULES:
        v = compiled / f"{name}.v"
        vo = compiled / f"{name}.vo"
        require(sha(vo) and vo.stat().st_mtime_ns > v.stat().st_mtime_ns
                and not re.search(r"\b(Admitted|admit|Axiom|sorry)\b", v.read_text()),
                f"missing/stale/forbidden certificate: {name}")
        if name in {"ReadyArrivalBaseAdapter", "ReadyArrivalCorrespondence"}:
            key = generated["generated"].get(name)
            if key is not None:
                require(key["output_sha256"] == sha(v),
                        f"generated adapter changed: {name}")
        else:
            require(sha(controlled / f"{name}.v") == sha(v),
                    f"controlled certificate changed: {name}")
    summary = read(W / "assumption_summary.json")
    audit_config = read(controlled / "concept_assumption_config.json")
    require(summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(audit_config["certificates"])
            and len(summary["certificates"]) == 24
            and "AUDIT_END" in (compiled / "ConceptAssumptionAudit.log").read_text(),
            "assumption log missing/truncated")
    allowed_status = {"CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
    for name, item in summary["certificates"].items():
        require(item["status"] in allowed_status
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"]
                and item["prop_sprop_foundation"] ==
                (["PropSPropFoundation.interpret_strict"]
                 if item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" else []),
                f"semantic gate failed: {name}")
    require(sum(x["status"] == "CERTIFIED" for x in summary["certificates"].values()) == 11
            and sum(x["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                    for x in summary["certificates"].values()) == 13,
            "per-certificate status count changed")
    inventory = read(W / "operation_inventory.json")
    require(inventory["status"] == "PASS" and inventory["declaration_count"] == 19
            and inventory["operation_count"] == inventory["covered_operation_count"] == 24
            and inventory["missing_operation_count"] == 0
            and inventory["invalid_bridges"] == {},
            "operation inventory not closed")
    require(not output("git", "-C", str(ROOT), "status", "--porcelain", "--",
                       "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    destination = V / "imported/translation_order/concept"
    require(not destination.exists(), "publication destination already exists")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".concept.", dir=destination.parent))
    for path in (exported, W / "export_metadata.json", wrapper, imported_vo,
                 W / "assumption_summary.json", W / "operation_inventory.json",
                 W / "source_build.log", lean_audit,
                 compiled / "ConceptAssumptionAudit.log"):
        shutil.copy2(path, stage / path.name)
    (stage / "certificates").mkdir()
    for name in MODULES:
        for suffix in (".v", ".vo"):
            shutil.copy2(compiled / f"{name}{suffix}",
                         stage / "certificates" / f"{name}{suffix}")
    require(sha(stage / exported.name) == sha(exported)
            and sha(stage / imported_vo.name) == sha(imported_vo),
            "staged artifact corruption")
    stage.rename(destination)

    def certificate_keys(name: str) -> list[str]:
        if name in PAIRED:
            return [name + "_import", name + "_export"]
        return [name]

    declarations = []
    for row in rows:
        name = row["declaration_name"]
        keys = certificate_keys(name)
        statuses = {summary["certificates"][key]["status"] for key in keys}
        require(len(statuses) == 1, f"two-sided status mismatch: {name}")
        status = statuses.pop()
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": f"Prosa.Model.Task.Concept.{name}",
            "kind": row["kind"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": type_evidence[row["qualified_name"]]["sha256"],
            "semantic_certificates": [audit_config["certificates"][key]["certificate"]
                                      for key in keys],
            "semantic_status": status,
            "semantic_premises": [],
            "statement_only_dependencies": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "prop_sprop_foundation":
                ["PropSPropFoundation.interpret_strict"]
                if status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION" else [],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    artifacts = {
        "official_source": official,
        "source_copy": source_copy,
        "source_vo": source_vo,
        "production_source": production,
        "production_olean": olean,
        "export_config": config_path,
        "export_metadata": destination / "export_metadata.json",
        "export": destination / exported.name,
        "imported_v": destination / wrapper.name,
        "imported_vo": destination / imported_vo.name,
        "assumption_summary": destination / "assumption_summary.json",
        "operation_inventory": destination / "operation_inventory.json",
        "lean_type_audit": destination / lean_audit.name,
        "assumption_config": controlled / "concept_assumption_config.json",
    }
    for name in MODULES:
        artifacts[f"{name}_v"] = destination / "certificates" / f"{name}.v"
        artifacts[f"{name}_vo"] = destination / "certificates" / f"{name}.vo"
    manifest = {
        "slice": "MODEL_TASK_CONCEPT",
        "source_commit": PIN,
        "source_file": SOURCE,
        "source_file_sha256": sha(official),
        "source_compatibility": "byte-identical official target source; accepted predecessor source package reused",
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": declarations,
        "operation_inventory_sha256": sha(destination / "operation_inventory.json"),
        "artifact_hashes": {key + "_sha256": sha(path) for key, path in artifacts.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT))
                           for key, path in artifacts.items() if path.is_relative_to(PROJECT)},
        "tooling_manifest_sha256": sha(V / "tooling/tooling_manifest.json"),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path = PIPE / "model_task_concept_module_manifest.json"
    status_path = PIPE / "model_task_concept_module_status.json"
    require(not manifest_path.exists() and not status_path.exists(),
            "formal machine publication already exists")
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 19, "translated": 19, "proof_clean": 19,
            "certified": sum(d["semantic_status"] == "CERTIFIED" for d in declarations),
            "certified_with_prop_sprop_foundation": sum(
                d["semantic_status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                for d in declarations),
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": {**previous["coverage"], "accepted_files": 58,
                     "accepted_declarations": 414},
        "previous_status": str((PIPE / "model_schedule_work_conserving_module_status.json")
                               .relative_to(PROJECT)),
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "accepted_files": 58,
                      "accepted_declarations": 414}, sort_keys=True))


if __name__ == "__main__":
    main()
