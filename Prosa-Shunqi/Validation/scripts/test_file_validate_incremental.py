#!/usr/bin/env python3
"""Validation-only regression for stage keys and sealed checkpoint integrity."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import tempfile
from pathlib import Path


def command(*args: str, success: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, text=True, capture_output=True)
    if (result.returncode == 0) != success:
        raise AssertionError({"argv": args, "returncode": result.returncode,
                              "stdout": result.stdout, "stderr": result.stderr})
    return result


def write(path: Path, value: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--validation", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    validation = args.validation.resolve()
    project = validation.parent
    exporter = validation / ".work/tooling/lean4export"
    actual_importer = validation / ".work/tooling/rocq-lean-import"
    source = validation / ".work/prosa-v06-414e667"
    stage_tool = validation / "scripts/prepare_stage_fingerprint.py"
    state_tool = validation / "scripts/incremental_validation_state.py"
    checks: dict[str, bool] = {}

    with tempfile.TemporaryDirectory(prefix="file_validate_regression_",
                                     dir=validation / ".work") as tmp:
        root = Path(tmp)
        rel = root.relative_to(validation).as_posix()
        importer = root / "importer"
        (importer / "src").mkdir(parents=True)
        for name in ("Lean.vo", "lean_import.cmxs"):
            shutil.copy2(actual_importer / "src" / name, importer / "src" / name)
        dummy = root / "prepared"
        write(dummy / "olean/Prosa/Util/Dummy.olean", "artifact-v1")
        write(dummy / "imported/Dummy.out", "export-v1")
        write(dummy / "imported/ImportedDummy.vo", "import-v1")
        write(dummy / "certificates/DummyCertificate.vo", "certificate-v1")
        config = root / "inputs.json"
        source_copy = root / "Dummy.lean"
        export_config = root / "export_config.json"
        import_fixture = root / "ImportedDummy.v"
        write(source_copy, "def dummy : Nat := 0\n")
        write(export_config, '{"target":"dummy"}\n')
        write(import_fixture, "From LeanImport Require Import Lean.\n")
        config.write_text(json.dumps({
            "inputs": [
                {"name": "lean_target", "root": "validation", "path": f"{rel}/Dummy.lean"},
                {"name": "source_dummy", "root": "source", "path": "util/notation.v"},
                {"name": "lean_toolchain", "root": "project", "path": "lean-toolchain"},
                {"name": "lakefile", "root": "project", "path": "lakefile.lean"},
                {"name": "lake_manifest", "root": "project", "path": "lake-manifest.json"},
                {"name": "dummy_export_config", "root": "validation", "path": f"{rel}/export_config.json"},
                {"name": "dummy_import_fixture", "root": "validation", "path": f"{rel}/ImportedDummy.v"},
                {"name": "lean4export", "root": "exporter", "path": ".lake/build/bin/lean4export"},
                {"name": "rocq_import", "root": "importer", "path": "src/lean_import.cmxs"},
                {"name": "rocq_foundation", "root": "importer", "path": "src/Lean.vo"},
            ], "module_loading": {"mode": "isolated"},
        }))

        def fingerprint(stage: str) -> str:
            return command(
                "python3", str(stage_tool), "--stage", stage,
                "--config", str(config), "--project", str(project),
                "--validation", str(validation), "--source", str(source),
                "--exporter", str(exporter), "--importer", str(importer),
                "--prepared", str(dummy), "--function-hash", "fixture-hook-v1",
            ).stdout.strip()

        initial = {stage: fingerprint(stage) for stage in
                   ("lean_build", "source_acquisition", "export", "rocq_import")}
        checks["identical_stage_inputs_hit_same_key"] = (
            initial == {stage: fingerprint(stage) for stage in initial})
        write(root / "DummyCertificate.v", "Definition test := True.\n")
        checks["certificate_edit_preserves_prepare_keys"] = (
            initial == {stage: fingerprint(stage) for stage in initial})
        write(source_copy, "def dummy : Nat := 1\n")
        changed = {stage: fingerprint(stage) for stage in initial}
        checks["lean_change_invalidates_build_key"] = (
            changed["lean_build"] != initial["lean_build"])
        write(export_config, '{"target":"dummy2"}\n')
        changed_export = fingerprint("export")
        checks["export_config_invalidates_export"] = changed_export != changed["export"]
        checks["export_config_preserves_build_key"] = (
            fingerprint("lean_build") == changed["lean_build"])
        write(import_fixture, "From LeanImport Require Import Lean. (* changed *)\n")
        checks["import_fixture_invalidates_import"] = (
            fingerprint("rocq_import") != changed["rocq_import"])
        foundation_before = fingerprint("rocq_import")
        with (importer / "src/Lean.vo").open("ab") as stream:
            stream.write(b"validation-only foundation mutation")
        checks["importer_foundation_invalidates_import"] = (
            fingerprint("rocq_import") != foundation_before)

        cache = root / "checkpoint"
        events = root / "events.jsonl"
        command("python3", str(state_tool), "seal-stage", "--prepared", str(dummy),
                "--cache", str(cache), "--snapshot-id", "snapshot-a",
                "--stage", "export", "--input-fingerprint", "export-key")
        (dummy / "imported/Dummy.out").unlink()
        command("python3", str(state_tool), "restore-stage", "--prepared", str(dummy),
                "--cache", str(cache), "--snapshot-id", "snapshot-b",
                "--stage", "export", "--input-fingerprint", "export-key",
                "--events", str(events), "--allow-cross-snapshot")
        checks["verified_checkpoint_restored"] = (
            (dummy / "imported/Dummy.out").read_text() == "export-v1")
        command("python3", str(state_tool), "restore-stage", "--prepared", str(dummy),
                "--cache", str(cache), "--snapshot-id", "snapshot-b",
                "--stage", "export", "--input-fingerprint", "wrong-key",
                "--events", str(events), "--allow-cross-snapshot", success=False)
        checks["wrong_input_key_rejected"] = True
        write(cache / "imported/Dummy.out", "corrupted")
        failed = command("python3", str(state_tool), "restore-stage", "--prepared", str(dummy),
                         "--cache", str(cache), "--snapshot-id", "snapshot-b",
                         "--stage", "export", "--input-fingerprint", "export-key",
                         "--events", str(events), "--allow-cross-snapshot", success=False)
        checks["corrupt_checkpoint_rejected"] = "HASH_MISMATCH" in failed.stderr

    result = {"status": "PASS" if all(checks.values()) else "FAIL", "checks": checks}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
