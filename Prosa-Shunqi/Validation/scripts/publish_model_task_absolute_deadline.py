#!/usr/bin/env python3
"""Fail-closed publication for the pinned absolute-deadline instance."""

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
WORK = V / ".work/experiments/model_task_absolute_deadline"
PIPE = V / "planning/v06_pipeline"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE = "model/task/absolute_deadline.v"
LEAN_NAME = "Prosa.Model.Task.AbsoluteDeadline.job_deadline_from_task_deadline"
LEAN_SHA = "7082807386bad75e5447ae3bfd2a8235cc17914949eaab95236f9e32bb41bb03"
OLEAN_SHA = "7e4d5c328512db4bdc51d548b0869b4efabf5c6b8a9f8cc7c645ea0ec1c46107"
EXPORT_SHA = "a1c8138c99a30c7a7aea0208c88c27405472d213d0037d23ee756580216a62bd"
CERTS = (
    "AbsoluteDeadlineBaseAdapter", "AbsoluteDeadlineCorrespondence",
    "AbsoluteDeadlineAssumptionAudit", "AbsoluteDeadlineTypeAudit",
)


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise SystemExit("ABSOLUTE_DEADLINE_PUBLICATION_REJECTED: " + reason)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def data(path: Path) -> dict:
    require(path.is_file(), f"missing {path}")
    return json.loads(path.read_text())


def command(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def main() -> None:
    official_root = V / ".work/prosa-v06-414e667"
    official = official_root / SOURCE
    source = WORK / "source" / SOURCE
    with (V / "planning/v06_dependency/file_inventory.csv").open() as stream:
        row = next(r for r in csv.DictReader(stream) if r["file"] == SOURCE)
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        declarations = [r for r in csv.DictReader(stream) if r["source_file"] == SOURCE]
    graph = data(V / "planning/v06_dependency/file_dag.json")
    deps = sorted(e["dependency_file"] for e in graph["edges"]
                  if e["dependent_file"] == SOURCE)
    require(deps == ["model/task/concept.v"] and row["layer"] == "11"
            and len(declarations) == 1
            and declarations[0]["declaration_name"] == "job_deadline_from_task_deadline"
            and declarations[0]["final_type_or_type_fingerprint"].startswith("rocq-check-sha256:"),
            "file DAG or elaborated public inventory changed")
    require(command("git", "-C", str(official_root), "rev-parse", "HEAD") == PIN
            and not command("git", "-C", str(official_root), "status", "--porcelain",
                            "--untracked-files=all")
            and sha(official) == row["sha256"] == sha(source),
            "pinned official source or source acquisition changed")
    concept = data(PIPE / "model_task_concept_module_manifest.json")
    stage = data(WORK / "accepted_concept_stage.json")
    require(concept["acceptance"] == "ACCEPTED_V06_FILE"
            and stage["concept_manifest_sha256"] ==
                sha(PIPE / "model_task_concept_module_manifest.json")
            and stage["target_source_sha256"] == sha(source)
            and stage["closure"][".olean"]["Model/Task/Concept.olean"] ==
                concept["production_olean_sha256"],
            "accepted Concept producer not bound")
    for kind, rels in stage["closure"].items():
        base = WORK / ("olean/Prosa" if kind == ".olean" else "source")
        for relative, expected in rels.items():
            require(sha(base / relative) == expected,
                    f"accepted dependency artifact changed: {relative}")
    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version")
            and command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                        "rev-parse", "HEAD") ==
                "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in command("opam", "exec", "--switch=rocq93rc1", "--",
                                 "rocq", "--version"), "toolchain changed")
    tooling = data(V / "tooling/tooling_manifest.json")
    require(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export") ==
                tooling["lean4export"]["expected_binary_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs") ==
                tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo") ==
                tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "export/import tooling changed")

    production = PROJECT / "Prosa/Model/Task/AbsoluteDeadline.lean"
    olean = WORK / "olean/Prosa/Model/Task/AbsoluteDeadline.olean"
    source_vo = source.with_suffix(".vo")
    source_guard = V / "fixtures/translation_order/AbsoluteDeadlineSourceTypeAudit.v"
    source_log = WORK / "source_type_audit.log"
    lean_guard = V / "fixtures/translation_order/AbsoluteDeadlineLeanTypeAudit.lean"
    lean_log = WORK / "lean_type_audit.log"
    require(sha(production) == LEAN_SHA and sha(olean) == OLEAN_SHA
            and olean.stat().st_mtime_ns > production.stat().st_mtime_ns
            and sha(source_vo) and source_vo.stat().st_mtime_ns > source.stat().st_mtime_ns
            and sha(source_guard) and sha(lean_guard)
            and "Closed under the global context" in source_log.read_text()
            and "job_deadline_from_task_deadline" in source_log.read_text()
            and not re.search(r"\b(sorry|admit|axiom|unsafe)\b", production.read_text()),
            "source/Lean freeze or proof-clean evidence failed")
    lean_output = lean_log.read_text()
    require(f"'{LEAN_NAME}' does not depend on any axioms" in lean_output
            and f"{LEAN_NAME} Job Task" in lean_output
            and "error:" not in lean_output.lower()
            and "#synth JobDeadline Job" in lean_guard.read_text()
            and "job_deadline j =" in lean_guard.read_text()
            and "rfl" in lean_guard.read_text(),
            "Lean proof-axiom, instance-selection, or field-computation guard failed")

    config = V / "tooling/model_task_absolute_deadline_export_config.json"
    cfg = data(config)
    meta = data(WORK / "export_metadata.json")
    exported = WORK / "imported/AbsoluteDeadline.out"
    imported_v = WORK / "imported/ImportedAbsoluteDeadline.v"
    imported_vo = WORK / "imported/ImportedAbsoluteDeadline.vo"
    require(cfg["module"] == "Prosa.Model.Task.AbsoluteDeadline"
            and LEAN_NAME in cfg["targets"] and cfg["statement_only"] == []
            and meta["config_sha256"] == sha(config)
            and meta["output_sha256"] == EXPORT_SHA == sha(exported)
            and sha(imported_v) ==
                sha(V / "certificates/model_task_absolute_deadline/ImportedAbsoluteDeadline.v")
            and sha(imported_vo)
            and imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns,
            "actual compiled export/import not bound")
    cert_dir = V / "certificates/model_task_absolute_deadline"
    for name in CERTS:
        src = cert_dir / f"{name}.v"
        vo = cert_dir / f"{name}.vo"
        require(sha(src) and sha(vo)
                and vo.stat().st_mtime_ns > src.stat().st_mtime_ns
                and vo.stat().st_mtime_ns > imported_vo.stat().st_mtime_ns
                and not re.search(r"\b(Axiom|Admitted|admit|sorry)\b", src.read_text()),
                f"certificate stale or contains proof gap: {name}")
    summary = data(WORK / "assumption_summary.json")
    log = WORK / "AbsoluteDeadlineAssumptionAudit.log"
    require(summary["audit_policy"] == "fail_closed"
            and len(summary["certificates"]) == 11
            and "AUDIT_END" in log.read_text()
            and summary["certificates"]["ad_job_deadline_from_task_deadline_certificate"]
                ["certificate"] == "ad_job_deadline_from_task_deadline_certificate",
            "assumption audit missing/truncated")
    for name, item in summary["certificates"].items():
        require(item["status"] == "CERTIFIED"
                and item["importer_foundation"] == ["Lean.eq"]
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"],
                f"assumption gate failed: {name}")
    proof = (cert_dir / "AbsoluteDeadlineCorrespondence.v").read_text()
    require("sub_add_correspondence" in proof
            and "AdJobTaskRel" in proof and "AdTaskDeadlineRel" in proof
            and "AdJobArrivalRel" in proof,
            "operation correspondence proof no longer compositional")
    require(not command("git", "-C", str(ROOT), "status", "--porcelain", "--",
                        "Prosa-fei"), "historical workspace changed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    accepted = []
    for path in PIPE.glob("*_module_status.json"):
        state = data(path)
        if state.get("status") == "PASS":
            coverage = state.get("coverage", {})
            accepted.append((coverage.get("accepted_files", -1),
                             coverage.get("accepted_declarations", -1), path))
    require(bool(accepted), "no accepted cumulative predecessor")
    previous_files, previous_decls, previous_path = max(accepted)
    require(sum((f, d) == (previous_files, previous_decls)
                for f, d, _ in accepted) == 1
            and (previous_files, previous_decls) == (67, 478),
            "accepted predecessor changed or ambiguous")
    previous = data(previous_path)
    destination = V / "imported/translation_order/absolute_deadline"
    manifest_path = PIPE / "model_task_absolute_deadline_module_manifest.json"
    status_path = PIPE / "model_task_absolute_deadline_module_status.json"
    require(not destination.exists() and not manifest_path.exists()
            and not status_path.exists(), "already published")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage_dir = Path(tempfile.mkdtemp(prefix=".absolute-deadline-", dir=destination.parent))
    evidence = {
        "source_vo": source_vo, "source_type_log": source_log,
        "production_olean": olean, "lean_type_log": lean_log,
        "export": exported, "export_metadata": WORK / "export_metadata.json",
        "imported_v": imported_v, "imported_vo": imported_vo,
        "assumption_log": log, "assumption_summary": WORK / "assumption_summary.json",
        "concept_stage": WORK / "accepted_concept_stage.json",
    }
    for key, original in list(evidence.items()):
        target = stage_dir / (key + original.suffix)
        shutil.copy2(original, target)
        require(sha(target) == sha(original), f"publication copy corrupted: {key}")
        evidence[key] = target
    (stage_dir / "certificates").mkdir()
    for name in CERTS:
        for suffix in (".v", ".vo"):
            original = cert_dir / (name + suffix)
            target = stage_dir / "certificates" / original.name
            shutil.copy2(original, target)
            require(sha(target) == sha(original), f"certificate copy corrupted: {name}")
            evidence[name + suffix] = target
    stage_dir.rename(destination)
    evidence = {key: destination / path.relative_to(stage_dir)
                for key, path in evidence.items()}
    target_row = declarations[0]
    manifest = {
        "slice": "MODEL_TASK_ABSOLUTE_DEADLINE", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": sha(official),
        "direct_file_dependencies": deps,
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(olean),
        "validation_mode": "FILE_VALIDATE_WITH_VERIFIED_ACCEPTED_PRODUCER",
        "target_build": "FRESH", "export": "FRESH", "rocq_import": "FRESH",
        "acceptance": "ACCEPTED_V06_FILE",
        "declarations": [{
            "source_declaration": target_row["qualified_name"],
            "kind": target_row["kind"],
            "source_command_sha256": target_row["source_command_sha256"],
            "source_elaborated_type_fingerprint":
                target_row["final_type_or_type_fingerprint"],
            "lean_declaration": LEAN_NAME,
            "semantic_certificate": "ad_job_deadline_from_task_deadline_certificate",
            "semantic_status": "CERTIFIED", "semantic_premises": [],
            "statement_only_dependencies": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "importer_foundation": ["Lean.eq"],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        }],
        "artifact_hashes": {k + "_sha256": sha(p) for k, p in evidence.items()},
        "artifact_paths": {k: str(p.relative_to(PROJECT)) for k, p in evidence.items()},
        "export_config_sha256": sha(config),
        "tooling_manifest_sha256": sha(V / "tooling/tooling_manifest.json"),
        "previous_status_file": previous_path.name,
        "previous_status_sha256": sha(previous_path),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = {**previous["coverage"],
                "accepted_files": previous_files + 1,
                "accepted_declarations": previous_decls + 1}
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {
            "public_declarations": 1, "translated": 1, "proof_clean": 1,
            "certified": 1, "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": coverage, "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "coverage": coverage}, sort_keys=True))


if __name__ == "__main__":
    main()
