#!/usr/bin/env python3
"""Fail-closed publication of the pinned PlatformProperties FILE_VALIDATE run."""

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
VALIDATION = PROJECT / "Validation"
WORK = VALIDATION / ".work/experiments/model_processor_platform_properties"
PIPE = VALIDATION / "planning/v06_pipeline"
SOURCE_FILE = "model/processor/platform_properties.v"
SOURCE_COMMIT = "414e66760333eaa4ef78c685bcf53291c527a548"
LEAN_MODULE = "Prosa.Model.Processor.PlatformProperties"
NAMES = (
    "unit_service_proc_model", "ideal_progress_proc_model",
    "uniprocessor_model", "unit_supply_proc_model",
    "unit_supply_is_unit_service", "fully_consuming_proc_model",
)
AUDIT_KEYS = (
    "platform_unit_service", "platform_ideal_progress",
    "platform_uniprocessor", "platform_unit_supply",
    "platform_unit_supply_implies_service", "platform_fully_consuming",
)
CERTS = (
    "unit_service_proc_model_correspondence",
    "ideal_progress_proc_model_correspondence",
    "uniprocessor_model_correspondence",
    "unit_supply_proc_model_correspondence",
    "unit_supply_is_unit_service_statement_correspondence",
    "fully_consuming_proc_model_correspondence",
)
GENERATED = (
    "PlatformScheduleBaseAdapter", "PlatformScheduleFiniteOperations",
    "PlatformScheduleCorrespondence", "PlatformProcessorStateCorrespondence",
)
HANDWRITTEN = (
    "PlatformPropertiesCorrespondence", "PlatformPropertiesExactTypeGuards",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(f"PLATFORM_PUBLICATION_REJECTED: {message}")


def sha(path: Path) -> str:
    require(path.is_file() and path.stat().st_size > 0, f"missing/empty {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def command(*argv: str) -> str:
    return subprocess.check_output(argv, text=True).strip()


def main() -> None:
    selection = read(PIPE / "model_processor_platform_properties_selection.json")
    baseline = read(PIPE / "model_processor_ideal_uni_exceed_module_status.json")
    require(selection["source_commit"] == SOURCE_COMMIT
            and selection["source_file"] == SOURCE_FILE
            and selection["rank"] == 51 and selection["file_dag_ready"]
            and selection["targets_in_source_order"] == list(NAMES),
            "selection or authoritative file DAG changed")
    require(baseline["status"] == "PASS"
            and baseline["coverage"]["accepted_files"] == 48
            and baseline["coverage"]["accepted_declarations"] == 353,
            "published baseline changed")

    source_root = VALIDATION / ".work/prosa-v06-414e667"
    official = source_root / SOURCE_FILE
    source_copy = WORK / "source" / SOURCE_FILE
    require(command("git", "-C", str(source_root), "rev-parse", "HEAD")
            == SOURCE_COMMIT
            and not command("git", "-C", str(source_root), "status", "--porcelain")
            and sha(official) == selection["source_sha256"]
            and sha(source_copy) == sha(official),
            "official source is not the pinned unmodified file")
    source_vo = source_copy.with_suffix(".vo")
    require(sha(source_vo) and source_vo.stat().st_mtime_ns >
            source_copy.stat().st_mtime_ns, "official Rocq source compile stale")
    source_type_log = WORK / "source_type_audit.log"
    require(sha(source_type_log), "missing source type audit")
    for name in NAMES:
        require(f"@{name}" in source_type_log.read_text(),
                f"source elaborated type not checked: {name}")

    with (VALIDATION / "planning/v06_dependency/declaration_inventory.csv").open() as stream:
        rows = [row for row in csv.DictReader(stream)
                if row["source_file"] == SOURCE_FILE]
    require([row["declaration_name"] for row in rows] == list(NAMES),
            "source declaration inventory mismatch")
    evidence = read(VALIDATION / "planning/v06_dependency/declaration_type_evidence.json")
    for row in rows:
        require(row["final_type_or_type_fingerprint"] ==
                "rocq-check-sha256:" + evidence[row["qualified_name"]]["sha256"],
                f"source type fingerprint changed: {row['declaration_name']}")

    olean_dir = WORK / "olean"
    reuse = read(WORK / "supply_reuse_evidence.json")
    require(reuse["status"] == "PASS" and reuse["mode"] == "VERIFIED_CACHE"
            and len(reuse["modules"]) == reuse["module_count"],
            "Supply dependency reuse evidence missing")
    for relative, expected in reuse["modules"].items():
        require(sha(olean_dir / relative) == expected,
                f"reused dependency artifact changed: {relative}")
    for base, module in (("behavior_service", "Service"),
                         ("behavior_ready", "Ready"),
                         ("behavior_all", "All"),
                         ("model_processor_supply", "Supply")):
        manifest = read(PIPE / f"{base}_module_manifest.json")
        require(manifest["acceptance"] == "ACCEPTED_V06_FILE"
                and sha(PROJECT / manifest["production_file"]) ==
                manifest["production_source_sha256"],
                f"accepted dependency changed: {base}")
        if base != "model_processor_supply":
            relative = f"Prosa/Behavior/{module}.olean"
            require(sha(olean_dir / relative) == manifest["production_olean_sha256"],
                    f"accepted dependency .olean changed: {relative}")

    require("Lean (version 4.33.1" in command("lake", "env", "lean", "--version")
            and command("git", "-C", str(PROJECT / ".lake/packages/mathlib"),
                        "rev-parse", "HEAD") ==
            "0df444a360eaa60ab8c11dca51a86af692955474"
            and "9.3" in command("opam", "exec", "--switch=rocq93rc1",
                                 "--", "rocq", "--version"),
            "toolchain changed")
    tooling = read(VALIDATION / "tooling/tooling_manifest.json")
    require(sha(VALIDATION / ".work/tooling/lean4export/.lake/build/bin/lean4export")
            == tooling["lean4export"]["expected_binary_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/lean_import.cmxs")
            == tooling["rocq_lean_import"]["expected_plugin_sha256"]
            and sha(VALIDATION / ".work/tooling/rocq-lean-import/src/Lean.vo")
            == tooling["rocq_lean_import"]["expected_foundation_vo_sha256"],
            "exporter/importer/foundation changed")

    production = PROJECT / "Prosa/Model/Processor/PlatformProperties.lean"
    target_olean = olean_dir / "Prosa/Model/Processor/PlatformProperties.olean"
    wrapper_olean = olean_dir / (
        "Validation/fixtures/translation_order/"
        "PlatformPropertiesComputationInterface.olean")
    require(production.stat().st_mtime_ns < target_olean.stat().st_mtime_ns
            < wrapper_olean.stat().st_mtime_ns,
            "target/interface Lean compilation stale")
    lean_audit_file = WORK / "lean_audit.log"
    lean_audit = lean_audit_file.read_text()
    require("error:" not in lean_audit and "sorryAx" not in lean_audit,
            "Lean audit failed")
    for name in NAMES:
        require(f"@{LEAN_MODULE}.{name} :" in lean_audit,
                f"Lean elaborated type missing: {name}")
        found = re.search(
            rf"'{re.escape(LEAN_MODULE)}\.{name}' depends on axioms: "
            r"\[([^]]+)\]", lean_audit)
        require(found is not None and
                {x.strip() for x in found.group(1).split(",")} ==
                {"propext", "Classical.choice", "Quot.sound"},
                f"Lean axiom set changed: {name}")

    export_config = VALIDATION / "tooling/model_processor_platform_properties_interface_export_config.json"
    config = read(export_config)
    export = WORK / "PlatformPropertiesWithInterface.out"
    export_meta_file = WORK / "interface_export_metadata.json"
    export_meta = read(export_meta_file)
    imported_dir = WORK / "imported"
    imported_out = imported_dir / export.name
    imported_v = imported_dir / "ImportedPlatformPropertiesWithInterface.v"
    imported_vo = imported_v.with_suffix(".vo")
    require(config["module"] ==
            "Validation.fixtures.translation_order.PlatformPropertiesComputationInterface"
            and len(config["targets"]) == 10
            and config["statement_only"] ==
            [f"{LEAN_MODULE}.unit_supply_is_unit_service"]
            and export_meta["config_sha256"] == sha(export_config)
            and export_meta["output_sha256"] == sha(export)
            and sha(imported_out) == sha(export)
            and 'Lean Import "PlatformPropertiesWithInterface.out".' in
            imported_v.read_text()
            and imported_vo.stat().st_mtime_ns >
            max(imported_out.stat().st_mtime_ns, imported_v.stat().st_mtime_ns),
            "actual imported Lean artifact stale or misbound")

    cert_dir = WORK / "certificates"
    for module in GENERATED + HANDWRITTEN:
        candidate = cert_dir / f"{module}.v"
        compiled = candidate.with_suffix(".vo")
        require(sha(candidate) and sha(compiled)
                and compiled.stat().st_mtime_ns > candidate.stat().st_mtime_ns,
                f"Rocq certificate stale: {module}")
        if module in HANDWRITTEN:
            require(sha(candidate) == sha(VALIDATION /
                    f"certificates/model_processor_platform_properties/{module}.v"),
                    f"checked-in certificate differs from compiled copy: {module}")
        require(not re.search(r"\b(sorry|Admitted|admit|Axiom|unsafe)\b",
                              candidate.read_text()),
                f"forbidden escape in {module}")
    require(not re.search(r"\b(sorry|Admitted|admit|axiom|unsafe)\b",
                          production.read_text()),
            "forbidden escape in production Lean")
    adapter = read(WORK / "platform_schedule_base_adapter.json")
    require(adapter["imported_artifact_sha256"] == sha(imported_vo)
            and adapter["semantic_assumptions_added"] == [],
            "generated adapter is not bound to imported artifact")
    instantiation = read(WORK / "schedule_instantiation.json")
    require(instantiation["imported_artifact_sha256"] == sha(imported_v)
            and len(instantiation["generated"]) == 3,
            "schedule correspondence instantiation stale")

    guard_log = WORK / "portable_PlatformPropertiesExactTypeGuards.log"
    require("source_unit_supply_is_unit_service_type_guard" in
            guard_log.read_text()
            and "target_unit_supply_is_unit_service_type_guard" in
            guard_log.read_text(), "source/target exact-type guard failed")
    assumption_log = WORK / "portable_PlatformPropertiesCorrespondence.log"
    assumptions = read(WORK / "assumption_summary.json")
    require(assumptions["audit_policy"] == "fail_closed"
            and set(assumptions["certificates"]) == set(AUDIT_KEYS),
            "assumption audit incomplete")
    for key in AUDIT_KEYS:
        item = assumptions["certificates"][key]
        require(item["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
                and item["prop_sprop_foundation"] == ["interpret_strict"]
                and item["semantic_premises"] == []
                and item["statement_only_dependencies"] == []
                and item["unexpected"] == []
                and not item["source_theorem_dependency"]
                and not item["target_theorem_dependency"],
                f"semantic assumption gate failed: {key}")
    budget = read(WORK / "interface_dependency_budget.json")
    require(budget["export_sha256"] == sha(export)
            and budget["explicit_export_root_count"] == 10
            and all(not x["imported_statement_only"] and
                    not x["unresolved_imported_assumptions"]
                    for x in budget["per_target_assumptions"].values()),
            "dependency budget/per-target statement-only audit stale")

    output = VALIDATION / "imported/translation_order/platform_properties"
    require(not output.exists(), f"publication target already exists: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=".platform_properties.", dir=output.parent))
    for source in (imported_out, imported_v, imported_vo, export_meta_file,
                   assumption_log, WORK / "assumption_summary.json",
                   WORK / "interface_dependency_budget.json", lean_audit_file,
                   source_type_log, guard_log,
                   WORK / "platform_schedule_base_adapter.json",
                   WORK / "schedule_instantiation.json"):
        shutil.copy2(source, temporary / source.name)
    (temporary / "certificates").mkdir()
    for module in GENERATED + HANDWRITTEN:
        for suffix in (".v", ".vo"):
            source = cert_dir / f"{module}{suffix}"
            shutil.copy2(source, temporary / "certificates" / source.name)
    require(sha(temporary / export.name) == sha(export)
            and sha(temporary / imported_vo.name) == sha(imported_vo),
            "publication copy corrupt")
    temporary.rename(output)

    artifact_paths = {
        "official_source": official,
        "source_vo": source_vo,
        "production_source": production,
        "production_olean": target_olean,
        "interface_source": VALIDATION / "fixtures/translation_order/PlatformPropertiesComputationInterface.lean",
        "interface_olean": wrapper_olean,
        "export_config": export_config,
        "export": output / export.name,
        "imported_v": output / imported_v.name,
        "imported_vo": output / imported_vo.name,
        "certificate_v": VALIDATION / "certificates/model_processor_platform_properties/PlatformPropertiesCorrespondence.v",
        "certificate_vo": output / "certificates/PlatformPropertiesCorrespondence.vo",
        "exact_type_guard_v": VALIDATION / "certificates/model_processor_platform_properties/PlatformPropertiesExactTypeGuards.v",
        "exact_type_guard_vo": output / "certificates/PlatformPropertiesExactTypeGuards.vo",
        "assumption_log": output / assumption_log.name,
        "assumption_summary": output / "assumption_summary.json",
        "budget": output / "interface_dependency_budget.json",
    }
    declarations = []
    for row, key, certificate in zip(rows, AUDIT_KEYS, CERTS, strict=True):
        name = row["declaration_name"]
        declarations.append({
            "source_declaration": row["qualified_name"],
            "source_command_sha256": row["source_command_sha256"],
            "source_elaborated_type_sha256": evidence[row["qualified_name"]]["sha256"],
            "kind": row["kind"],
            "lean_declaration": f"{LEAN_MODULE}.{name}",
            "semantic_certificate": certificate,
            "input_relations": ["SchProcessorStateRel", "SubNatRel",
                                "SchBoolRel", "PropSPropRel"],
            "semantic_status": assumptions["certificates"][key]["status"],
            "prop_sprop_foundation": ["PropSPropFoundation.interpret_strict"],
            "semantic_premises": [],
            "statement_only_dependencies": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "unexpected_assumptions": [],
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })
    manifest = {
        "source_file": SOURCE_FILE,
        "source_commit": SOURCE_COMMIT,
        "rank": 51,
        "acceptance": "ACCEPTED_V06_FILE",
        "build_mode": "FILE_VALIDATE",
        "dependency_reuse": "VERIFIED_CACHE",
        "target_build": "FRESH",
        "interface_build": "FRESH",
        "source_acquisition": "PINNED_UNMODIFIED_DIRECT_COMPILE",
        "translation_file": str(production.relative_to(PROJECT)),
        "certificate_file": "Validation/certificates/model_processor_platform_properties/PlatformPropertiesCorrespondence.v",
        "proof_clean": True,
        "actual_compiled_artifact_imported": True,
        "declarations": declarations,
        "artifact_hashes": {key: sha(path) for key, path in artifact_paths.items()},
        "artifact_paths": {key: str(path.relative_to(PROJECT))
                           for key, path in artifact_paths.items()},
        "accepted_dependency_manifest_sha256": {
            base: sha(PIPE / f"{base}_module_manifest.json")
            for base in ("behavior_all", "model_processor_supply")
        },
        "supply_reuse_evidence_sha256": sha(WORK / "supply_reuse_evidence.json"),
        "tooling_manifest_sha256": sha(VALIDATION / "tooling/tooling_manifest.json"),
        "published_at": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    }
    manifest_file = PIPE / "model_processor_platform_properties_module_manifest.json"
    manifest_file.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    coverage = dict(baseline["coverage"])
    coverage["accepted_files"] += 1
    coverage["accepted_declarations"] += len(NAMES)
    status = {
        "slice": "MODEL_PROCESSOR_PLATFORM_PROPERTIES",
        "status": "PASS",
        "manifest_sha256": sha(manifest_file),
        "coverage": coverage,
        "per_file": {
            SOURCE_FILE: {
                "status": "ACCEPTED_V06_FILE",
                "public_declarations": len(NAMES),
                "translated": len(NAMES),
                "proof_clean": len(NAMES),
                "certified": len(NAMES),
                "certified_with_prop_sprop_foundation": len(NAMES),
            }
        },
    }
    status_file = PIPE / "model_processor_platform_properties_module_status.json"
    status_file.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "accepted_files": coverage["accepted_files"],
                      "accepted_declarations": coverage["accepted_declarations"],
                      "published": str(output)}, sort_keys=True))


if __name__ == "__main__":
    main()
