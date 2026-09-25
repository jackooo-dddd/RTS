#!/usr/bin/env python3
"""Fail-closed publication of the v0.6 basic-readiness module interface."""

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
from string import Template


PROJECT = Path(__file__).resolve().parents[2]
ROOT = PROJECT.parent
V = PROJECT / "Validation"
WORK = V / ".work/experiments/model_readiness_basic"
PIPE = V / "planning/v06_pipeline"
CERT = V / "certificates/model_readiness_basic"
PIN = "414e66760333eaa4ef78c685bcf53291c527a548"
SOURCE = "model/readiness/basic.v"
LEAN_SHA = "5a66ed32baf9a0f6fe7588f0d71f27abe22e6cf8a7abbc6d0807385d2f26ca1b"
OLEAN_SHA = "48125a49b59a5e4d7e97d78fe3da30f265511329c667202f5b5a8385e51b34fc"
EXPORT_SHA = "e34025aae0f77959dc58e20663acf5f7abdd5af7df286b3f30e38debcd065838"
REPLAY = ("BasicBaseAdapter", "BasicNatBoolOperations",
          "BasicIntervalOperations", "BasicScheduleOperations",
          "BasicJobOperations")
COMMON = ("PropSPropFoundation", "LogicalRelation",
          "SubadditivityNatCorrespondence")
FORMAL = ("ReadinessBasicInterfaceCertificate", "BasicPendingCorrespondence",
          "BasicPendingAssumptionAudit")


def need(condition: bool, why: str) -> None:
    if not condition:
        raise SystemExit("READINESS_BASIC_PUBLICATION_REJECTED: " + why)


def sha(path: Path) -> str:
    need(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def data(path: Path) -> dict:
    return json.loads(path.read_text())


def run(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def remove_block(text: str, start: str, stop: str) -> str:
    need(text.count(start) == text.count(stop) == 1,
         f"generated subset boundary changed: {start}")
    a, b = text.index(start), text.index(stop)
    need(a < b, f"generated subset order changed: {start}")
    return text[:a] + text[b:]


def expected_replay(name: str, imported_sha: str) -> str:
    source_name = name.replace("Basic", "Service", 1)
    source = V / f"certificates/behavior_service/{source_name}.v"
    source_rel = source.relative_to(PROJECT)
    text = source.read_text()
    replacements = {
        "ImportedService": "ImportedReadinessBasicProjection",
        "ServiceBaseAdapter": "BasicBaseAdapter",
        **{f"Service{x}": f"Basic{x}" for x in
           ("NatBoolOperations", "IntervalOperations", "ScheduleOperations",
            "JobOperations", "Correspondence")},
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    if name == "BasicNatBoolOperations":
        text = remove_block(text, "Lemma svc_bool_or_related", "Lemma svc_target_add_related")
        line = "Print Assumptions svc_bool_or_related.\n"
        need(text.count(line) == 1, "Bool.or audit line changed")
        text = text.replace(line, "")
    if name == "BasicJobOperations":
        text = remove_block(text, "Definition SvcJobDeadlineRel", "Lemma svc_has_arrived_related")
        text = remove_block(text, "Lemma svc_arrived_before_related", "Goal Logic.True.")
        for line in ("Print Assumptions svc_job_deadline_import.\n",
                     "Print Assumptions svc_job_deadline_export.\n",
                     "Print Assumptions svc_arrived_before_related.\n"):
            need(text.count(line) == 1, f"unused Job operation audit changed: {line}")
            text = text.replace(line, "")
    return ("(** GENERATED ARTIFACT-LOCAL INSTANTIATION.\n"
            f"    source: {source_rel}\n"
            f"    source-sha256: {sha(source)}\n"
            f"    imported-artifact-sha256: {imported_sha} *)\n" + text)


def main() -> None:
    selection = data(PIPE / "model_readiness_basic_selection.json")
    need(selection["source_commit"] == PIN and selection["source_file"] == SOURCE
         and selection["rank"] == 55 and selection["layer"] == 10
         and selection["file_dag_ready"]
         and selection["direct_internal_dependencies"] == ["behavior/all.v"]
         and selection["public_declaration_count"] == 0
         and selection["nonpublic_downstream_interface"] == ["basic_ready_instance"],
         "selection, file DAG, or local-interface inventory changed")
    with (V / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        need(not any(row["source_file"] == SOURCE for row in csv.DictReader(stream)),
             "public declaration inventory changed")
    official_root = V / ".work/prosa-v06-414e667"
    official = official_root / SOURCE
    copied = WORK / "source" / SOURCE
    need(run("git", "-C", str(official_root), "rev-parse", "HEAD") == PIN
         and not run("git", "-C", str(official_root), "status", "--porcelain",
                     "--untracked-files=all")
         and sha(official) == selection["source_sha256"]
         and official.read_text().count("  Next Obligation. by done. Qed.\n") == 1
         and official.read_text().replace("  Next Obligation. by done. Qed.\n", "")
             == copied.read_text()
         and sha(V / "patches/prosa-v06-rocq93-model-readiness-basic.patch"),
         "pinned source or proof-only Rocq 9.3 compatibility copy changed")
    source_vo = copied.with_suffix(".vo")
    source_log = WORK / "source_type_audit.log"
    need(sha(source_vo) and source_vo.stat().st_mtime_ns > copied.stat().st_mtime_ns
         and "@basic_ready_instance" in source_log.read_text()
         and "basic_ready_instance =" in source_log.read_text()
         and "Error:" not in source_log.read_text(),
         "source interface/fidelity audit missing")
    behavior = data(PIPE / "behavior_all_module_manifest.json")
    need(behavior["acceptance"] == "ACCEPTED_V06_FILE"
         and sha(PROJECT / behavior["production_file"]) ==
             behavior["production_source_sha256"]
         and sha(WORK / "olean/Prosa/Behavior/All.olean") ==
             behavior["production_olean_sha256"],
         "authoritative file-DAG dependency not accepted/current")
    need("Lean (version 4.33.1" in run("lake", "env", "lean", "--version")
         and run("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                 "rev-parse", "HEAD") ==
             "0df444a360eaa60ab8c11dca51a86af692955474"
         and "9.3" in run("opam", "exec", "--switch=rocq93rc1", "--",
                          "rocq", "--version"), "toolchain changed")
    tooling = data(V / "tooling/tooling_manifest.json")
    need(sha(V / ".work/tooling/lean4export/.lake/build/bin/lean4export") ==
             tooling["lean4export"]["expected_binary_sha256"]
         and sha(V / ".work/tooling/rocq-lean-import/src/lean_import.cmxs") ==
             tooling["rocq_lean_import"]["expected_plugin_sha256"]
         and sha(V / ".work/tooling/rocq-lean-import/src/Lean.vo") ==
             tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
         "export/import tooling changed")

    production = PROJECT / "Prosa/Model/Readiness/Basic.lean"
    target_olean = WORK / "olean/Prosa/Model/Readiness/Basic.olean"
    lean_log = WORK / "lean_audit.log"
    need(sha(production) == LEAN_SHA and sha(target_olean) == OLEAN_SHA
         and target_olean.stat().st_mtime_ns > production.stat().st_mtime_ns
         and not re.search(r"\b(sorry|axiom|unsafe|admit)\b", production.read_text())
         and "'Prosa.Model.Readiness.Basic.basic_ready_instance' depends on axioms: "
             "[propext, Classical.choice, Quot.sound]" in lean_log.read_text()
         and "Error:" not in lean_log.read_text(),
         "production source, proof-clean, or compiled target changed")
    for staged in (WORK / "olean/Prosa").rglob("*.olean"):
        if staged == target_olean:
            continue
        relative = staged.relative_to(WORK / "olean")
        source_name = relative.with_suffix(".lean")
        matches = [data(path) for path in PIPE.glob("*_module_manifest.json")
                   if data(path).get("production_file") == str(source_name)]
        need(len(matches) == 1 and matches[0]["acceptance"] == "ACCEPTED_V06_FILE"
             and sha(PROJECT / source_name) == matches[0]["production_source_sha256"]
             and sha(staged) == matches[0]["production_olean_sha256"],
             f"staged dependency .olean not accepted: {relative}")
    for module in ("Schedule", "Service", "ReadinessBasic"):
        interface = V / f"fixtures/translation_order/{module}ComputationInterface.lean"
        compiled = WORK / f"olean/Validation/fixtures/translation_order/{module}ComputationInterface.olean"
        need(sha(interface) and sha(compiled)
             and compiled.stat().st_mtime_ns > interface.stat().st_mtime_ns,
             f"kernel computation guard stale: {module}")
    config = V / "tooling/model_readiness_basic_projection_export_config.json"
    meta = data(WORK / "export_metadata.json")
    exported = WORK / "imported/ReadinessBasicProjection.out"
    imported = WORK / "imported/ImportedReadinessBasicProjection.vo"
    need(sha(exported) == EXPORT_SHA == meta["output_sha256"]
         and meta["config_sha256"] == sha(config)
         and meta["statement_only_count"] == 0
         and meta["body_theorem_count"] == 2
         and meta["exporter_sha256"] ==
             tooling["lean4export"]["expected_binary_sha256"]
         and WORK.joinpath("export.log").read_text().count("kernel_rfl_guard=true") >= 6
         and sha(imported) and imported.stat().st_mtime_ns > exported.stat().st_mtime_ns,
         "actual guarded export/import artifact changed or stale")

    base = WORK / "certificates/BasicBaseAdapter.v"
    base_meta = data(WORK / "certificates/basic_base_adapter.json")
    template = V / "templates/ArtifactBoolListAdapter.v.tpl"
    rendered = Template(template.read_text()).substitute(
        IMPORTED="ImportedReadinessBasicProjection", PREFIX="svc", CAP="Svc")
    need(base.read_text() == rendered
         and base_meta["template_sha256"] == sha(template)
         and base_meta["imported_artifact_sha256"] == EXPORT_SHA
         and base_meta["output_sha256"] == sha(base)
         and base_meta["semantic_assumptions_added"] == [],
         "generated Bool/List/equality adapter not reproducibly bound")
    for name in REPLAY[1:]:
        actual = WORK / f"certificates/{name}.v"
        need(actual.read_text() == expected_replay(name, EXPORT_SHA),
             f"accepted Service operation replay changed: {name}")
    for name in COMMON + REPLAY:
        original = (V / "certificates/common" if name in COMMON
                    else WORK / "certificates") / f"{name}.v"
        staged = WORK / f"certificates/{name}.v"
        compiled = WORK / f"certificates/{name}.vo"
        need(sha(original) == sha(staged) and sha(compiled)
             and compiled.stat().st_mtime_ns > staged.stat().st_mtime_ns
             and compiled.stat().st_mtime_ns > imported.stat().st_mtime_ns,
             f"bridge source/compiled proof changed: {name}")
        if name != "PropSPropFoundation":
            need(not re.search(r"\b(Axiom|Admitted|admit|sorry)\b", staged.read_text()),
                 f"forbidden proof gap in bridge: {name}")
    for name in FORMAL:
        source = CERT / f"{name}.v"
        compiled = ((WORK / "certificates") if name == FORMAL[0] else CERT) / f"{name}.vo"
        need(sha(source) and sha(compiled)
             and compiled.stat().st_mtime_ns > source.stat().st_mtime_ns
             and compiled.stat().st_mtime_ns > imported.stat().st_mtime_ns
             and not re.search(r"\b(Axiom|Admitted|admit|sorry)\b", source.read_text()),
             f"formal certificate stale or contains a gap: {name}")
    interface_summary = data(WORK / "readiness_basic_interface_assumption_summary.json")
    pending_summary = data(WORK / "basic_pending_assumption_summary.json")
    need(interface_summary["audit_policy"] == pending_summary["audit_policy"] == "fail_closed"
         and len(interface_summary["certificates"]) == 7
         and len(pending_summary["certificates"]) == 8
         and sha(WORK / "certificates/ReadinessBasicInterfaceCertificate.log")
         and sha(WORK / "BasicPendingAssumptionAudit.log"),
         "source/target interface or cross-ITP assumption audit missing")
    for item in list(interface_summary["certificates"].values()) + \
                list(pending_summary["certificates"].values()):
        need(item["status"] in ("CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")
             and item["semantic_premises"] == []
             and item["statement_only_dependencies"] == []
             and item["unexpected"] == []
             and not item["source_theorem_dependency"]
             and not item["target_theorem_dependency"]
             and item["prop_sprop_foundation"] in
               ([], ["PropSPropFoundation.interpret_strict"]),
             f"assumption gate failed: {item['certificate']}")
    need(pending_summary["certificates"]["basic_ready_field"]["status"] ==
             "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
         and pending_summary["certificates"]["basic_ready_law"]["status"] ==
             "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
         and not run("git", "-C", str(ROOT), "status", "--porcelain", "--", "Prosa-fei"),
         "field/law relation or historical-workspace integrity failed")
    subprocess.run(["git", "-C", str(ROOT), "diff", "--check"], check=True)

    accepted = []
    for path in PIPE.glob("*_module_status.json"):
        state = data(path)
        if state.get("status") == "PASS":
            c = state.get("coverage", {})
            accepted.append((c.get("accepted_files", -1),
                             c.get("accepted_declarations", -1), path))
    need(bool(accepted), "no accepted predecessor")
    files, decls, predecessor = max(accepted)
    need((files, decls) == (68, 479)
         and sum((f, d) == (files, decls) for f, d, _ in accepted) == 1,
         "accepted predecessor changed or ambiguous")
    destination = V / "imported/translation_order/readiness_basic"
    manifest_path = PIPE / "model_readiness_basic_module_manifest.json"
    status_path = PIPE / "model_readiness_basic_module_status.json"
    need(not destination.exists() and not manifest_path.exists()
         and status_path.exists() and data(status_path)["status"] == "PARTIAL",
         "module already published or partial baseline changed")
    destination.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".readiness-basic-", dir=destination.parent))
    evidence = {
        "official_source": official, "compatibility_source": copied,
        "source_vo": source_vo, "source_type_log": source_log,
        "lean_source": production, "target_olean": target_olean,
        "lean_audit_log": lean_log, "export": exported,
        "export_metadata": WORK / "export_metadata.json",
        "imported_vo": imported, "imported_v": imported.with_suffix(".v"),
        "interface_summary": WORK / "readiness_basic_interface_assumption_summary.json",
        "pending_summary": WORK / "basic_pending_assumption_summary.json",
        "pending_audit_log": WORK / "BasicPendingAssumptionAudit.log",
        "base_adapter_metadata": WORK / "certificates/basic_base_adapter.json",
    }
    copied_evidence = {}
    for key, source in evidence.items():
        target = stage / (key + source.suffix)
        shutil.copy2(source, target)
        need(sha(target) == sha(source), f"published evidence corrupted: {key}")
        copied_evidence[key] = target
    (stage / "certificates").mkdir()
    for name in COMMON + REPLAY + FORMAL:
        original_dir = (V / "certificates/common" if name in COMMON
                        else CERT if name in FORMAL else WORK / "certificates")
        for suffix in (".v", ".vo"):
            original = original_dir / (name + suffix)
            if name == FORMAL[0] and suffix == ".vo":
                original = WORK / "certificates" / (name + suffix)
            target = stage / "certificates" / original.name
            shutil.copy2(original, target)
            need(sha(target) == sha(original), f"published certificate corrupted: {name}")
            copied_evidence[name + suffix] = target
    stage.rename(destination)
    paths = {key: destination / path.relative_to(stage)
             for key, path in copied_evidence.items()}
    manifest = {
        "slice": "MODEL_READINESS_BASIC", "source_commit": PIN,
        "source_file": SOURCE, "source_file_sha256": sha(official),
        "source_compatibility": "proof-only Rocq 9.3 removal of obsolete Next Obligation",
        "source_compatibility_patch_sha256":
            sha(V / "patches/prosa-v06-rocq93-model-readiness-basic.patch"),
        "direct_file_dependencies": ["behavior/all.v"],
        "production_file": str(production.relative_to(PROJECT)),
        "production_source_sha256": sha(production),
        "production_olean_sha256": sha(target_olean),
        "export_config_sha256": sha(config),
        "actual_export_sha256": sha(exported),
        "validation_mode": "VERIFIED_TARGET_COMPILE_REUSED_FRESH_GUARDED_EXPORT_IMPORT",
        "target_build": "VERIFIED_CACHE", "export": "FRESH", "rocq_import": "FRESH",
        "acceptance": "ACCEPTED_V06_FILE", "declarations": [],
        "nonpublic_downstream_interface": {
            "source": "prosa.model.readiness.basic.basic_ready_instance",
            "lean": "Prosa.Model.Readiness.Basic.basic_ready_instance",
            "imported": "ImportedReadinessBasicProjection.Prosa_Model_Readiness_Basic_basic_ready_instance",
            "field_certificate": "basic_ready_field_correspondence",
            "law_statement_certificate": "basic_ready_law_statement_correspondence",
            "semantic_status": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
            "semantic_premises": [], "statement_only_dependencies": [],
            "source_theorem_dependency": False, "target_theorem_dependency": False,
            "unexpected_assumptions": [],
        },
        "artifact_hashes": {key + "_sha256": sha(path) for key, path in paths.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT)) for key, path in paths.items()},
        "previous_status_file": predecessor.name,
        "previous_status_sha256": sha(predecessor),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    prior = data(predecessor)
    coverage = {**prior["coverage"], "accepted_files": files + 1,
                "accepted_declarations": decls}
    status = {
        "slice": manifest["slice"], "status": "PASS",
        "per_file": {SOURCE: {"public_declarations": 0,
                              "nonpublic_downstream_interfaces": 1,
                              "translated": 1, "proof_clean": 1,
                              "certified": 1, "status": "ACCEPTED_V06_FILE"}},
        "coverage": coverage, "manifest_sha256": sha(manifest_path),
    }
    status_path.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "coverage": coverage}, sort_keys=True))


if __name__ == "__main__":
    main()
