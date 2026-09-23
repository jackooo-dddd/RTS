#!/usr/bin/env python3
"""Seal a successful isolated Fixpoint fresh run for snapshot-aware publication."""

import argparse
import hashlib
import json
from pathlib import Path


def sha(path: Path) -> str:
    if not path.is_file() or not path.stat().st_size:
        raise SystemExit(f"MISSING_OR_EMPTY_ARTIFACT:{path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    project = args.project.resolve()
    validation = project / "Validation"
    work = args.work.resolve()
    source = validation / ".work/prosa-v06-414e667/util/fixpoint.v"
    source_rel = validation / ".work/prosa-v06-414e667/util/rel.v"
    lean = project / "Prosa/Util/Fixpoint.lean"
    interface = validation / "fixtures/translation_order/FixpointComputationInterface.lean"
    config = validation / "tooling/util_fixpoint_export_config.json"
    exporter = validation / ".work/tooling/lean4export/.lake/build/bin/lean4export"
    importer = validation / ".work/tooling/rocq-lean-import/src/lean_import.cmxs"
    foundation = validation / ".work/tooling/rocq-lean-import/src/Lean.vo"
    build = work / "lean_source_build_manifest.json"
    build_data = json.loads(build.read_text())
    if build_data.get("status") != "PASS" or build_data.get("producer_mode") != "CLEAN_FULL":
        raise SystemExit("FRESH_BUILD_MANIFEST_INVALID")
    for relative, item in build_data["modules"].items():
        if sha(work / "olean" / relative) != item["sha256"]:
            raise SystemExit(f"FRESH_MODULE_HASH_MISMATCH:{relative}")
        if sha(project / item["source_path"]) != item["source_sha256"]:
            raise SystemExit(f"FRESH_MODULE_SOURCE_CHANGED:{relative}")
    required = [
        "Prosa/Util/Fixpoint.olean",
        "Validation/fixtures/translation_order/FixpointComputationInterface.olean",
    ]
    if any(name not in build_data["modules"] for name in required):
        raise SystemExit("FRESH_BUILD_INCOMPLETE")
    metadata = json.loads((work / "source/GeneratedFixpointSourceAll_extraction.json").read_text())
    if (metadata.get("source_commit") != "414e66760333eaa4ef78c685bcf53291c527a548"
            or metadata.get("source_file_sha256") != sha(source)
            or len(metadata.get("declarations", {})) != 17):
        raise SystemExit("SOURCE_EXTRACTION_FIDELITY_FAILED")
    for name, row in metadata["declarations"].items():
        if row["source_kind"] == "theorem" and row.get("elaborated_type_evidence") != "ELABORATED_ROCQ_CHECK":
            raise SystemExit(f"SOURCE_TYPE_NOT_ELABORATED:{name}")
        if row["source_kind"] == "computational" and row["source_block_sha256"] != row["generated_text_sha256"]:
            raise SystemExit(f"SOURCE_BODY_CHANGED:{name}")
    inputs = {
        "source": sha(source), "source_rel": sha(source_rel),
        "source_type_evidence": sha(validation / "planning/v06_dependency/declaration_type_evidence.json"),
        "source_extractor": sha(validation / "scripts/extract_v06_semantic_source.py"),
        "validator": sha(validation / "scripts/validate_utility_fixpoint.sh"),
        "validation_common": sha(validation / "scripts/common/validation_common.sh"),
        "build_manifest_sealer": sha(validation / "scripts/file_validate_lean_dependencies.py"),
        "lean": sha(lean), "interface": sha(interface),
        "export_config": sha(config), "exporter": sha(exporter),
        "importer": sha(importer), "foundation": sha(foundation),
        "import_wrapper": sha(validation / "fixtures/translation_order/ImportedFixpoint.v"),
        "accepted_nat_export": sha(validation / "imported/utility_foundation/Nat.out"),
        "accepted_subadd_export": sha(validation / "imported/foundation_slice_2_closure/Subadditivity.out"),
        "toolchain": sha(project / "lean-toolchain"),
        "lakefile": sha(project / "lakefile.lean"),
        "lake_manifest": sha(project / "lake-manifest.json"),
        "build_manifest": sha(build),
    }
    snapshot = digest(inputs)
    output_groups = {
        "lean_build": {
            "lean_source_build_manifest.json": sha(build),
            "olean/Prosa/Util/Fixpoint.olean": sha(work / "olean/Prosa/Util/Fixpoint.olean"),
            "olean/Validation/fixtures/translation_order/FixpointComputationInterface.olean":
                sha(work / "olean/Validation/fixtures/translation_order/FixpointComputationInterface.olean"),
        },
        "source_acquisition": {
            "source/GeneratedFixpointSourceAll.v": sha(work / "source/GeneratedFixpointSourceAll.v"),
            "source/GeneratedFixpointSourceAll.vo": sha(work / "source/GeneratedFixpointSourceAll.vo"),
            "source/GeneratedFixpointSourceAll_extraction.json":
                sha(work / "source/GeneratedFixpointSourceAll_extraction.json"),
        },
        "export": {"imported/Fixpoint.out": sha(work / "imported/Fixpoint.out")},
        "rocq_import": {"imported/ImportedFixpoint.vo": sha(work / "imported/ImportedFixpoint.vo")},
    }
    timing_file = validation / "logs/translation_order/fixpoint/module_build_timing.jsonl"
    timings = [json.loads(line) for line in timing_file.read_text().splitlines() if line]
    final_modules = timings[-9:]
    expected_modules = [f"Prosa.Util.{name}" for name in
        ["Tactics", "Nat", "Notation", "Rel", "Supremum", "List", "Setoid", "Minmax", "Fixpoint"]]
    if ([row["module"] for row in final_modules] != expected_modules
            or any(row["status"] != "PASS" or row["mode"] != "FRESH" for row in final_modules)):
        raise SystemExit("FRESH_MODULE_TIMING_EVIDENCE_MISSING")
    outputs = {stage: {"files": files} for stage, files in output_groups.items()}
    manifest = {
        "snapshot_id": snapshot, "mode": "CLEAN_FULL", "inputs": inputs,
        "outputs": outputs, "module_build_timings": final_modules,
    }
    evidence = {
        "snapshot_id": snapshot,
        "stages": [
            {"stage": stage, "mode": "FRESH", "executed": True,
             "input_fingerprint": digest({"snapshot": snapshot, "stage": stage}),
             "output_hashes": files,
             "elapsed_seconds": sum(row["elapsed_seconds"] for row in final_modules)
             if stage == "lean_build" else None}
            for stage, files in output_groups.items()
        ],
    }
    (work / "prepare_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (work / "prepare_run_evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(snapshot)


if __name__ == "__main__":
    main()
