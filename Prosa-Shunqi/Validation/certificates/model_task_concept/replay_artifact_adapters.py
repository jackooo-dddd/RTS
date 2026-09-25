#!/usr/bin/env python3
"""Instantiate the pinned arrival adapters for an actual Concept import.

This writes only to the caller-supplied, target-private scratch directory.  It
does not build, publish, or alter any accepted certificate or formal status.
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


BASE_SHA = "f61754c8275be1d2d537179bba2bee314510939cee5d7065756d3b4b93bf9c6d"
CORRESPONDENCE_SHA = "5b5f0de2cf8a7f00dbbd6809c8e96ef8ae0d368a0b87801f8a3657d9493ff453"
LEMMAS = (
    "arrivals_at_correspondence_certificate",
    "arrives_at_correspondence_certificate",
    "arrives_in_correspondence_certificate",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--imported-artifact", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()

    root = args.source_root.resolve()
    artifact = args.imported_artifact.resolve()
    output = args.output_dir.resolve()
    base = root / "Validation/certificates/behavior_ready/ReadyArrivalBaseAdapter.v"
    arr_dir = root / "Validation/certificates/behavior_arrival_sequence"
    correspondence = arr_dir / "ArrivalSequenceCorrespondence.v"
    if digest(base) != BASE_SHA or digest(correspondence) != CORRESPONDENCE_SHA:
        raise SystemExit("accepted arrival adapter/correspondence source hash mismatch")
    if not artifact.is_file() or artifact.stat().st_size == 0:
        raise SystemExit("actual imported Concept artifact missing")
    output.mkdir(parents=True, exist_ok=True)

    body = base.read_text()
    if body.startswith("(** GENERATED ARTIFACT-LOCAL INSTANTIATION."):
        body = body[body.index("*)") + 2 :].lstrip("\n")
    body = body.replace("ImportedReady", "ImportedTaskConcept")
    base_output = output / "ReadyArrivalBaseAdapter.v"
    base_output.write_text(
        "(** Replayed accepted Bool/List/EqType adapter for exact Concept import.\n"
        f"    source-sha256: {BASE_SHA}\n"
        f"    imported-artifact-sha256: {digest(artifact)} *)\n" + body
    )

    metadata = output / "concept_arrival_instantiation.json"
    command = [
        sys.executable,
        str(root / "Validation/scripts/instantiate_arrival_correspondence.py"),
        "--source-dir", str(arr_dir),
        "--output-dir", str(output),
        "--imported-module", "ImportedTaskConcept",
        "--imported-artifact", str(artifact),
        "--metadata", str(metadata),
    ]
    for lemma in LEMMAS:
        command.extend(("--correspondence-lemma", lemma))
    subprocess.run(command, check=True)

    selected = output / "ReadyArrivalCorrespondence.v"
    text = selected.read_text()
    old = "  ReadyArrivalOperations."
    if text.count(old) != 1:
        raise SystemExit("arrival correspondence operation-import shape changed")
    selected.write_text(text.replace(old, "  ConceptOperations."))
    report = json.loads(metadata.read_text())
    report["generated"]["ReadyArrivalCorrespondence"]["output_sha256"] = digest(selected)
    report["concept_operation_import_replacement"] = {
        "from": old.strip(), "to": "ConceptOperations.", "count": 1
    }
    report["concept_base_adapter"] = {
        "source_sha256": BASE_SHA,
        "output_sha256": digest(base_output),
        "imported_artifact_sha256": digest(artifact),
    }
    metadata.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
