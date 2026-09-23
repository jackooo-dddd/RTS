#!/usr/bin/env python3
"""Replay accepted Nat subtraction/division bridges on one imported artifact.

Only imported module identity and DivMod's now-unused ImportedNat import
change. Both generated proofs must be independently recompiled and audited.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
SOURCES = PROJECT / "Validation/certificates/common"
MANIFEST = PROJECT / "Validation/planning/v06_pipeline/div_mod_module_manifest.json"
EXPECTED = {
    "NatSubCorrespondence.v": "7d8700c52d59ff709996d96f2e9d3bd88e76d4c3914808fbeaf4866a68f22d57",
    "DivModCorrespondence.v": "56f67cf73fd04427254a82142b2190465eae8d453d828a084d7360ce48d02404",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--imported", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    if not args.imported.isidentifier() or not args.imported.startswith("Imported"):
        raise SystemExit("invalid imported module name")
    manifest = json.loads(MANIFEST.read_text())
    if manifest.get("acceptance") != "ACCEPTED_V06_FILE":
        raise SystemExit("DivMod producer is not accepted")
    for name, expected in EXPECTED.items():
        source = SOURCES / name
        if digest(source) != expected or expected not in MANIFEST.read_text():
            raise SystemExit(f"unmatched accepted source hash: {name}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for name, old in (("NatSubCorrespondence.v", "ImportedNat"),
                      ("DivModCorrespondence.v", "ImportedDivMod")):
        source = SOURCES / name
        content = source.read_text()
        if old not in content:
            raise SystemExit(f"missing imported identity: {name}")
        content = content.replace(old, args.imported)
        if name.startswith("DivMod"):
            content = content.replace(f"{args.imported} ImportedNat ImportedSubadditivity",
                                      f"{args.imported} ImportedSubadditivity")
        header = ("(** Mechanical replay of accepted bridge source " + EXPECTED[name]
                  + "; imported identity " + old + " -> " + args.imported
                  + ". DivMod drops the unused ImportedNat import. *)\n")
        output = args.output_dir / name
        output.write_text(header + content)
        print(f"{name}: {digest(output)}")


if __name__ == "__main__":
    main()
