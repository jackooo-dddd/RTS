#!/usr/bin/env python3
"""Replay a hash-accepted operation certificate against a new import identity.

The generated Rocq source is compiled normally; the rewrite does not assert
semantic equivalence.  It changes only the imported-module qualifier, which
is unavoidable because independent lean4export imports create distinct Rocq
List/Prod/Bool constants for the same compiled Lean dependencies.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha(path: Path) -> str:
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit(f"missing/empty source: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--accepted-manifest", required=True, type=Path)
    parser.add_argument("--source-certificate", required=True, type=Path)
    parser.add_argument("--old-imported", required=True)
    parser.add_argument("--new-imported", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    manifest = json.loads(args.accepted_manifest.read_text())
    if manifest.get("acceptance") != "ACCEPTED_V06_FILE":
        raise SystemExit("certificate producer is not a published accepted file")
    expected = manifest["artifact_hashes"]["certificate_source_sha256"]
    if sha(args.source_certificate) != expected:
        raise SystemExit("accepted operation certificate source hash changed")
    source = args.source_certificate.read_text()
    old = args.old_imported
    new = args.new_imported
    if old == new or source.count(old) < 10 or new in source:
        raise SystemExit("non-unique or absent imported-module identity substitution")
    generated = (
        "(** GENERATED artifact-local replay of the accepted operation "
        "certificate.\n"
        f"    Producer certificate SHA-256: {expected}.\n"
        f"    Sole substitution: {old} -> {new}.\n"
        "    This generated source is recompiled and assumption-audited; "
        "it is not a trusted axiom. *)\n"
        + source.replace(old, new)
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(generated)
    print(json.dumps({"source_sha256": expected,
                      "output_sha256": sha(args.output),
                      "substitutions": source.count(old)}, indent=2))


if __name__ == "__main__":
    main()
