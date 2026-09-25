#!/usr/bin/env python3
"""Replay the accepted Supply interval proof against this exact Lean import.

This is a mechanical source-generation step, not a trusted proof.  Both
outputs must compile and pass Print Assumptions for the new imported artifact.
"""

import argparse
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    if not path.is_file() or not path.stat().st_size:
        raise SystemExit(f"missing or empty input: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--artifact", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    artifact_hash = digest(args.artifact.resolve())
    accepted = project / "Validation/planning/v06_pipeline/model_processor_supply_module_manifest.json"
    if json.loads(accepted.read_text()).get("acceptance") != "ACCEPTED_V06_FILE":
        raise SystemExit("Supply interval proof producer is not accepted")
    source_dir = project / "Validation/certificates/model_processor_supply"
    expected = {
        "SupplyNatBoolOperations.v": "db563b7aef812eb438fa51b4cc8425a1f6bb8b73d7ea1c1a87192ada5659c5f6",
        "SupplyIntervalOperations.v": "5c47194e726a1cfb28461296ea724a07c1032e53f17f8a006336c5c0072ba9b5",
    }
    replacements = {
        "ImportedSupply": "ImportedAbstractDefinitions",
        "SupplyBaseAdapter": "AbstractDefinitionsBaseAdapter",
        "SupplyNatBoolOperations": "AbstractDefinitionsNatBoolOperations",
        "SvcBoolRel": "AdBoolRel",
        "svc_coq_false_to_target": "ad_coq_false_to_target",
        "svc_false_elim": "ad_false_elim",
        "svc_false_ne_true": "ad_false_ne_true",
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, expected_hash in expected.items():
        source = source_dir / name
        if digest(source) != expected_hash:
            raise SystemExit(f"accepted proof source changed: {source}")
        body = source.read_text()
        if name == "SupplyIntervalOperations.v":
            body = body[body.index("From mathcomp Require Import") :]
        for old, new in replacements.items():
            body = body.replace(old, new)
        output = args.output_dir / name.replace("Supply", "AbstractDefinitions", 1)
        output.write_text(
            "(** GENERATED proof replay, not an axiom.\n"
            f"    accepted source SHA-256: {expected_hash}\n"
            f"    imported artifact SHA-256: {artifact_hash}. *)\n" + body
        )
        print(f"{output}: {digest(output)}")


if __name__ == "__main__":
    main()
