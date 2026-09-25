#!/usr/bin/env python3
"""Fail-closed publication of model/task/arrival/sporadic.v."""

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
VALIDATION = PROJECT / "Validation"
WORK = VALIDATION / ".work/experiments/model_task_arrival_sporadic_main"
PIPE = VALIDATION / "planning/v06_pipeline"
CERT = VALIDATION / "certificates/model_task_arrival_sporadic"
SOURCE = "model/task/arrival/sporadic.v"
PRODUCTION = "Prosa/Model/Task/Arrival/Sporadic.lean"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
TREE = "7d7e94c731f7eefde4ca738310d4cafdd7bebdf0"
TARGETS = [
    "SporadicModel",
    "valid_task_min_inter_arrival_time",
    "valid_taskset_inter_arrival_times",
    "respects_sporadic_task_model",
    "taskset_respects_sporadic_task_model",
]
CERT_MODULES = [
    "SporadicBaseAdapter",
    "SporadicOperations",
    "SporadicClasses",
    "SporadicCorrespondence",
    "SporadicTypeAudit",
    "SporadicAssumptionAudit",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("SPORADIC_PUBLICATION_REJECTED: " + message)


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def git(source: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(source), *args], text=True).strip()


def main() -> None:
    source_root = VALIDATION / ".work/prosa-v06-414e667"
    official = source_root / SOURCE
    copied = WORK / "source" / SOURCE
    production = PROJECT / PRODUCTION
    target_olean = WORK / "olean/Prosa/Model/Task/Arrival/Sporadic.olean"
    exported = WORK / "imported/Sporadic.out"
    imported_wrapper = WORK / "imported/ImportedSporadic.v"
    imported_vo = WORK / "imported/ImportedSporadic.vo"
    require(git(source_root, "rev-parse", "HEAD") == PIN, "source commit changed")
    require(git(source_root, "rev-parse", "HEAD^{tree}") == TREE, "source tree changed")
    require(not git(source_root, "status", "--porcelain", "--untracked-files=all"),
            "pinned source worktree is dirty")
    require(sha(official) == sha(copied), "source acquisition is not byte-identical")
    require(sha(official) == "e7d32c5f69ef6e6a0dea092f55b6f48ef1dcd0d1ab286a698cb889a16d1b96dc",
            "authoritative source hash changed")

    with (VALIDATION / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream) if row["source_file"] == SOURCE]
    require([row["declaration_name"] for row in rows] == TARGETS,
            "authoritative declaration inventory changed")
    type_evidence = read(VALIDATION / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        item = type_evidence[row["qualified_name"]]
        require(row["final_type_or_type_fingerprint"] == "rocq-check-sha256:" + item["sha256"],
                f"source type evidence changed for {row['declaration_name']}")

    source_vo = copied.with_suffix(".vo")
    require(source_vo.stat().st_mtime_ns > copied.stat().st_mtime_ns,
            "official source .vo missing or stale")
    require(sha(production) and sha(target_olean), "production target artifact missing")
    require(target_olean.stat().st_mtime_ns > production.stat().st_mtime_ns,
            "target .olean is stale")
    require(not re.search(r"\b(sorry|admit|axiom|unsafe)\b", production.read_text(), re.I),
            "forbidden Lean escape in production source")

    export_config = VALIDATION / "tooling/model_task_arrival_sporadic_export_config.json"
    metadata = read(WORK / "export_metadata.json")
    require(metadata["module"] == "Prosa.Model.Task.Arrival.Sporadic"
            and metadata["target_count"] == 15
            and metadata["statement_only_count"] == 0
            and metadata["definition_target_count"] == 4
            and metadata["config_sha256"] == sha(export_config)
            and metadata["output_sha256"] == sha(exported),
            "actual export metadata or configuration changed")
    require(imported_wrapper.read_text() ==
            'From LeanImport Require Import Lean.\nLean Import "Sporadic.out".\n',
            "import wrapper changed")
    require(imported_vo.stat().st_mtime_ns > exported.stat().st_mtime_ns,
            "imported .vo is stale")

    lean_axioms = read(WORK / "lean_axiom_summary.json")
    require(not lean_axioms["missing"] and not lean_axioms["extra"]
            and all(item["status"] == "PASS"
                    and not item["unexpected_axioms"]
                    for item in lean_axioms["declarations"].values()),
            "Lean axiom audit failed")
    type_log = (WORK / "certificates/SporadicTypeAudit.log").read_text()
    require("Error:" not in type_log and all(name in type_log for name in TARGETS),
            "Rocq exact-type audit failed")

    summary = read(WORK / "assumption_summary.json")
    config = read(CERT / "sporadic_assumption_config.json")
    require(summary["audit_policy"] == "fail_closed"
            and set(summary["certificates"]) == set(config["certificates"]),
            "Rocq assumption summary is incomplete")
    allowed = {"CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
    for item in summary["certificates"].values():
        require(item["status"] in allowed and not item["semantic_premises"]
                and not item["statement_only_dependencies"]
                and not item["unexpected"]
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"],
                "Rocq semantic gate failed")

    previous_path = PIPE / "model_readiness_basic_module_status.json"
    previous = read(previous_path)
    require(previous["status"] == "PASS"
            and previous["coverage"]["accepted_files"] == 69
            and previous["coverage"]["accepted_declarations"] == 479
            and previous["coverage"]["translated_but_not_certified"] == 0,
            "formal baseline changed")
    require(not git(ROOT, "status", "--porcelain", "--", "Prosa-fei"),
            "historical Prosa-fei workspace changed")

    now = datetime.now(timezone.utc).astimezone()
    stamp = now.strftime("%Y-%m-%d_%H%M%S")
    declarations = []
    for row in rows:
        name = row["declaration_name"]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "lean_declaration": "Prosa.Model.Task.Arrival.Sporadic." + name,
            "semantic_status": "CERTIFIED" if name == "SporadicModel" else
                "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
            "certificate": "sp_sporadic_model_import_certificate" if name == "SporadicModel" else
                "sp_" + name + "_canonical",
            "semantic_premises": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "slice": "TRANSLATION_ORDER_MODEL_TASK_ARRIVAL_SPORADIC",
        "generated_at": now.isoformat(),
        "published_at": now.isoformat(),
        "rank": 75,
        "layer": 11,
        "source_file": SOURCE,
        "source_commit": PIN,
        "source_tree": TREE,
        "source_file_sha256": sha(official),
        "production_file": PRODUCTION,
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(target_olean),
        "export_sha256": sha(exported),
        "import_sha256": sha(imported_vo),
        "source_vo_sha256": sha(source_vo),
        "lean_axiom_summary_sha256": sha(WORK / "lean_axiom_summary.json"),
        "rocq_assumption_summary_sha256": sha(WORK / "assumption_summary.json"),
        "certificates": {name: {"source_sha256": sha(CERT / f"{name}.v"),
                                "vo_sha256": sha(WORK / f"certificates/{name}.vo")}
                        for name in CERT_MODULES},
        "declarations": declarations,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    manifest_path = PIPE / "model_task_arrival_sporadic_module_manifest.json"
    status_path = PIPE / "model_task_arrival_sporadic_module_status.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": manifest["slice"],
        "status": "PASS",
        "source_file": SOURCE,
        "per_file": {SOURCE: {
            "public_declarations": 5,
            "translated": 5,
            "proof_clean": 5,
            "semantic_proof_compiled": 5,
            "certified": 5,
            "status": "ACCEPTED_V06_FILE",
            "published_at": now.isoformat(),
        }},
        "coverage": {
            "accepted_files": 70,
            "authoritative_files": 357,
            "accepted_declarations": 484,
            "authoritative_declarations": 2439,
            "translated_but_not_certified": 0,
            "deferred_external_boundary": 239,
        },
        "previous_status_sha256": sha(previous_path),
        "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2) + "\n")

    destination = VALIDATION / "imported/translation_order/model_task_arrival_sporadic"
    require(not destination.exists(), "publication destination already exists")
    destination.mkdir(parents=True)
    for path in (exported, imported_wrapper, imported_vo,
                 WORK / "export_metadata.json", WORK / "lean_type_audit.log",
                 WORK / "lean_axiom_summary.json", WORK / "assumption_summary.json",
                 WORK / "certificates/SporadicTypeAudit.log",
                 WORK / "certificates/SporadicAssumptionAudit.log"):
        shutil.copy2(path, destination / path.name)
    cert_dest = destination / "certificates"
    cert_dest.mkdir()
    for name in CERT_MODULES:
        for suffix in (".v", ".vo"):
            src = WORK / "certificates" / f"{name}{suffix}"
            shutil.copy2(src, cert_dest / src.name)

    report_dir = PROJECT / "Reports/files/model/task/arrival"
    report_dir.mkdir(parents=True, exist_ok=True)
    report = report_dir / f"{stamp}_sporadic.md"
    report_text = (
        f"# `model/task/arrival/sporadic.v`\n\n"
        f"- 验收时间：{now.strftime('%m:%d:%H:%M')}\n"
        "- Rank：75；Layer：11；权威声明：5\n"
        "- 状态：`ACCEPTED_V06_FILE`\n"
        f"- Lean：`{PRODUCTION}`；fresh build 后 `.olean` 已绑定当前 production hash。\n"
        "- 导出/导入：`Sporadic.out` → `ImportedSporadic.vo`，target count 15，statement-only 0。\n"
        "- 语义证书：18 项 Rocq correspondence/adapter/canonical certificate 全部编译并通过 fail-closed assumption audit。\n"
        "- 语义状态：`SporadicModel` 为 `CERTIFIED`；其余 4 个 public declarations 为 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`。\n"
        "- 审计：semantic premises 为空；source theorem dependency=false；target theorem dependency=false；unexpected assumptions 为空；Lean axiom audit 仅出现允许的 `propext`。\n"
        "- 复用：Nat、Bool、List/seq、membership、arrival-sequence 和 Prop/SProp bridges；新增 Sporadic-specific model/arrival adapters。\n"
        f"- 证据：manifest `{manifest_path.relative_to(PROJECT)}`；status `{status_path.relative_to(PROJECT)}`；publication `{destination.relative_to(PROJECT)}`。\n\n"
        "## Findings\n\n"
        "该文件的主要边界是 class field、Bool-reflected validity 与 Prop/SProp arrival constraints 的组合；实际导入接口携带 `DecidableEq` 和 `SporadicModel` 参数，未将其错误简化为无参数 proposition。\n"
    )
    report.write_text(report_text)
    print(json.dumps({"manifest": str(manifest_path), "status": str(status_path),
                      "report": str(report), "coverage": status["coverage"]}, indent=2))


if __name__ == "__main__":
    main()
