#!/usr/bin/env python3
"""Recheck accepted Ready/Arrival proofs against a fresh WorkConserving import.

This only generates target-local Rocq source.  The caller must kernel-compile
the output against the supplied imported artifact; no status is published.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

READY_HASHES = {
    "ReadyBaseAdapter": "badae59a40333a5319dad6179d06849e58a7b1b296b818d5fb523b4ad03f2478",
    "ReadyNatBoolOperations": "592e22ab3b273ed96e8eed7e7eeb01ed4be346e9328e6cd8ce4a30715412b533",
    "ReadyIntervalOperations": "71a5dd7a8cef4e2359e6a03d474bc72ad25657eb1896a77f060d7404c9d76ef3",
    "ReadyScheduleOperations": "6beb52b6d2071285c99f9c5bea2a125eb12da11a1b6e340cd1a2048b4829169e",
    "ReadyJobOperations": "92315b0ac8caddf6e30a63760152425069a3a9f2e8f6467bffa1becc82274191",
    "ReadyServiceCorrespondence": "747555c503ac2c0f1eb882a8e5dbe786ade2067626bfd50a44fb19a3c3f1205f",
    "ReadyArrivalBaseAdapter": "f61754c8275be1d2d537179bba2bee314510939cee5d7065756d3b4b93bf9c6d",
    "ReadyCorrespondence": "eead5d12fda3c184d85f3f215470cc637e298565b2d85cfcb0d3f9c2615942ae",
}
ARRIVAL_HASHES = {
    "ArrivalSequenceOperations": "b3d8a9f93976846f1777182c55f59b73872f912d8a2534c69e65d1dcbd1778cc",
    "ArrivalSequenceCorrespondence": "5b5f0de2cf8a7f00dbbd6809c8e96ef8ae0d368a0b87801f8a3657d9493ff453",
}
ARRIVAL_GENERATOR_HASH = "68c66bc8eb7aba2577d7cf68921d07afe695fcef971bc5b67a0e3768b023d720"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(path: Path, expected: str) -> None:
    if not path.is_file() or sha(path) != expected:
        raise SystemExit(f"fixed-input hash mismatch: {path}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-root", required=True, type=Path)
    parser.add_argument("--imported-artifact", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    root = args.project_root.resolve()
    artifact = args.imported_artifact.resolve()
    output = args.output_dir.resolve()
    if not artifact.is_file() or not artifact.stat().st_size:
        raise SystemExit("imported WorkConserving artifact absent or empty")
    ready_source = root / "Validation/certificates/behavior_ready"
    arrival_source = root / "Validation/certificates/behavior_arrival_sequence"
    arrival_generator = root / "Validation/scripts/instantiate_arrival_correspondence.py"
    for name, expected in READY_HASHES.items():
        checked(ready_source / f"{name}.v", expected)
    for name, expected in ARRIVAL_HASHES.items():
        checked(arrival_source / f"{name}.v", expected)
    checked(arrival_generator, ARRIVAL_GENERATOR_HASH)

    output.mkdir(parents=True, exist_ok=True)
    generated = {}
    artifact_hash = sha(artifact)
    for name, source_hash in READY_HASHES.items():
        source = ready_source / f"{name}.v"
        target = output / f"{name}.v"
        body = source.read_text()
        if body.startswith("(** GENERATED ARTIFACT-LOCAL INSTANTIATION."):
            body = body[body.index("*)") + 2:].lstrip("\n")
        body = body.replace("ImportedReady", "ImportedWorkConserving")
        target.write_text(
            "(** Mechanically replayed accepted Ready proof for the exact imported artifact.\n"
            f"    source-sha256: {source_hash}\n"
            f"    imported-artifact-sha256: {artifact_hash} *)\n" + body
        )
        generated[name] = {"source_sha256": source_hash, "output_sha256": sha(target)}

    subprocess.run([
        sys.executable, str(arrival_generator),
        "--source-dir", str(arrival_source),
        "--output-dir", str(output),
        "--imported-module", "ImportedWorkConserving",
        "--imported-artifact", str(artifact),
        "--correspondence-lemma", "arrivals_at_correspondence_certificate",
        "--correspondence-lemma", "arrives_at_correspondence_certificate",
        "--correspondence-lemma", "arrives_in_correspondence_certificate",
        "--correspondence-lemma", "arrivals_between_correspondence_certificate",
        "--correspondence-lemma", "arrivals_up_to_correspondence_certificate",
        "--metadata", str(output / "work_conserving_arrival_instantiation.json"),
    ], check=True)
    (output / "work_conserving_ready_instantiation.json").write_text(json.dumps({
        "schema_version": 1,
        "method": "kernel_rechecked_artifact_local_replay",
        "imported_artifact": str(artifact),
        "imported_artifact_sha256": artifact_hash,
        "generated": generated,
    }, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
