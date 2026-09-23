#!/usr/bin/env python3
"""Mutation checks for an accepted FILE_VALIDATE dependency producer."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import tempfile
from pathlib import Path


def call(argv: list[str], expected: int) -> str:
    result = subprocess.run(argv, capture_output=True, text=True)
    if result.returncode != expected:
        raise AssertionError({"argv": argv, "expected": expected,
                              "actual": result.returncode, "stderr": result.stderr})
    return result.stderr


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--validation", required=True, type=Path)
    parser.add_argument("--producer-name", required=True)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--status", required=True, type=Path)
    parser.add_argument("--module", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    validation = args.validation.resolve()
    accepted = json.loads(args.manifest.read_text())
    original = validation / ".work/incremental" / args.producer_name / accepted["snapshot_id"]
    if not (original / "lean_source_build_manifest.json").is_file():
        raise SystemExit("accepted producer has no source/module build manifest")
    tool = validation / "scripts/file_validate_lean_dependencies.py"
    checks: dict[str, bool] = {}
    with tempfile.TemporaryDirectory(prefix="file_validate_producer_",
                                     dir=validation / ".work") as tmp:
        root = Path(tmp)
        producer = root / "producer"
        producer.mkdir()
        for name in ("lean_source_build_manifest.json", "prepare_manifest.json"):
            shutil.copy2(original / name, producer / name)
        shutil.copytree(original / "olean", producer / "olean")
        accepted_copy = root / "accepted_manifest.json"
        shutil.copy2(args.manifest, accepted_copy)

        def run(expected: int) -> str:
            destination = root / "consumer"
            if destination.exists():
                shutil.rmtree(destination)
            destination.mkdir()
            return call([
                "python3", str(tool), "materialize",
                "--project", str(validation.parent), "--producer", str(producer),
                "--accepted-manifest", str(accepted_copy),
                "--accepted-status", str(args.status),
                "--destination", str(destination), "--module", args.module,
                "--evidence", str(root / "reuse_evidence.json"),
            ], expected)

        run(0)
        checks["accepted_producer_reused"] = (
            json.loads((root / "reuse_evidence.json").read_text())["module_count"] > 0)

        artifact = producer / "olean" / (args.module.replace(".", "/") + ".olean")
        original_artifact = artifact.read_bytes()
        artifact.write_bytes(original_artifact + b"damaged")
        checks["artifact_corruption_rejected"] = (
            "PRODUCER_ARTIFACT_CORRUPT" in run(3))
        artifact.write_bytes(original_artifact)

        build_path = producer / "lean_source_build_manifest.json"
        build = json.loads(build_path.read_text())
        build["producer_mode"] = "TAMPERED"
        build_path.write_text(json.dumps(build, indent=2, sort_keys=True) + "\n")
        checks["build_manifest_seal_mismatch_rejected"] = (
            "PRODUCER_BUILD_MANIFEST_SEAL_MISMATCH" in run(3))
        shutil.copy2(original / "lean_source_build_manifest.json", build_path)

        wrong_acceptance = dict(accepted)
        wrong_acceptance["production_olean_sha256"] = "0" * 64
        accepted_copy.write_text(json.dumps(wrong_acceptance, indent=2) + "\n")
        checks["accepted_artifact_mismatch_rejected"] = (
            "PRODUCER_ACCEPTED_ARTIFACT_MISMATCH" in run(3))

    outcome = {"status": "PASS" if all(checks.values()) else "FAIL", "checks": checks}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(outcome, indent=2, sort_keys=True) + "\n")
    print(json.dumps(outcome, sort_keys=True))
    if outcome["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
