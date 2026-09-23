#!/usr/bin/env python3
"""Seal the isolated, freshly built util/superadditivity.v validation run."""

import argparse
import hashlib
import json
from pathlib import Path


def sha(path: Path) -> str:
    if not path.is_file() or not path.stat().st_size:
        raise SystemExit(f"MISSING_OR_EMPTY:{path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def digest(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    project, work = args.project.resolve(), args.work.resolve()
    validation = project / "Validation"
    source = validation / ".work/prosa-v06-414e667/util/superadditivity.v"
    build = work / "lean_source_build_manifest.json"
    build_data = json.loads(build.read_text())
    if (build_data.get("status") != "PASS"
            or build_data.get("producer_mode") != "CLEAN_FULL"):
        raise SystemExit("FRESH_BUILD_MANIFEST_INVALID")
    required = {
        "Prosa/Util/Superadditivity.olean",
        "Validation/fixtures/translation_order/SuperadditivityComputationInterface.olean",
    }
    if not required.issubset(build_data["modules"]):
        raise SystemExit("FRESH_BUILD_INCOMPLETE")
    for relative, item in build_data["modules"].items():
        if (sha(work / "olean" / relative) != item["sha256"]
                or sha(project / item["source_path"]) != item["source_sha256"]):
            raise SystemExit(f"FRESH_BUILD_INPUT_OR_OUTPUT_CHANGED:{relative}")
    metadata_path = work / "source/OfficialSuperadditivityAll_extraction.json"
    metadata = json.loads(metadata_path.read_text())
    if (metadata.get("source_commit") !=
            "414e66760333eaa4ef78c685bcf53291c527a548"
            or metadata.get("source_file_sha256") != sha(source)
            or len(metadata.get("declarations", {})) != 12):
        raise SystemExit("SOURCE_EXTRACTION_FIDELITY_FAILED")
    for name, row in metadata["declarations"].items():
        if (row["source_kind"] == "theorem"
                and row.get("elaborated_type_evidence") != "ELABORATED_ROCQ_CHECK"):
            raise SystemExit(f"SOURCE_TYPE_NOT_ELABORATED:{name}")
        if (row["source_kind"] == "computational"
                and row["source_block_sha256"] != row["generated_text_sha256"]):
            raise SystemExit(f"SOURCE_BODY_CHANGED:{name}")
    inputs = {
        "source": sha(source),
        "source_type_evidence": sha(validation / "planning/v06_dependency/declaration_type_evidence.json"),
        "source_extractor": sha(validation / "scripts/extract_v06_semantic_source.py"),
        "validation_common": sha(validation / "scripts/common/validation_common.sh"),
        "build_manifest_sealer": sha(validation / "scripts/file_validate_lean_dependencies.py"),
        "lean": sha(project / "Prosa/Util/Superadditivity.lean"),
        "interface": sha(validation / "fixtures/translation_order/SuperadditivityComputationInterface.lean"),
        "export_config": sha(validation / "tooling/util_superadditivity_interface_export_config.json"),
        "exporter": sha(validation / ".work/tooling/lean4export/.lake/build/bin/lean4export"),
        "importer": sha(validation / ".work/tooling/rocq-lean-import/src/lean_import.cmxs"),
        "foundation": sha(validation / ".work/tooling/rocq-lean-import/src/Lean.vo"),
        "import_wrapper": sha(validation / "fixtures/translation_order/ImportedSuperadditivity.v"),
        "accepted_nat_export": sha(validation / "imported/utility_foundation/Nat.out"),
        "accepted_subadd_export": sha(validation / "imported/foundation_slice_2_closure/Subadditivity.out"),
        "toolchain": sha(project / "lean-toolchain"),
        "lakefile": sha(project / "lakefile.lean"),
        "lake_manifest": sha(project / "lake-manifest.json"),
        "build_manifest": sha(build),
    }
    snapshot = digest(inputs)
    outputs = {
        "lean_build": {
            "lean_source_build_manifest.json": sha(build),
            **{f"olean/{name}": sha(work / "olean" / name)
               for name in sorted(build_data["modules"])},
        },
        "source_acquisition": {
            "source/OfficialSuperadditivityAll.v":
                sha(work / "source/OfficialSuperadditivityAll.v"),
            "source/OfficialSuperadditivityAll.vo":
                sha(work / "source/OfficialSuperadditivityAll.vo"),
            "source/OfficialSuperadditivityAll_extraction.json": sha(metadata_path),
        },
        "export": {"imported/Superadditivity.out":
                   sha(work / "imported/Superadditivity.out")},
        "rocq_import": {"imported/ImportedSuperadditivity.vo":
                        sha(work / "imported/ImportedSuperadditivity.vo")},
    }
    export_meta = json.loads((work / "export_interface_metadata.json").read_text())
    if (export_meta["output_sha256"] != outputs["export"]["imported/Superadditivity.out"]
            or export_meta["config_sha256"] != inputs["export_config"]
            or export_meta["exporter_sha256"] != inputs["exporter"]):
        raise SystemExit("EXPORT_PROVENANCE_MISMATCH")
    manifest = {"snapshot_id": snapshot, "mode": "CLEAN_FULL", "inputs": inputs,
                "outputs": {stage: {"files": files} for stage, files in outputs.items()}}
    evidence = {"snapshot_id": snapshot, "stages": [
        {"stage": stage, "mode": "FRESH", "executed": True,
         "input_fingerprint": digest({"snapshot": snapshot, "stage": stage}),
         "output_hashes": files, "elapsed_seconds": None}
        for stage, files in outputs.items()
    ]}
    (work / "prepare_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (work / "prepare_run_evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(snapshot)


if __name__ == "__main__":
    main()
