#!/usr/bin/env python3
"""Replay accepted Rocq certificate source against a new imported artifact.

This is a mechanical module-identity rewrite, not a semantic assumption.
The generated files must be compiled and assumption-audited independently.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit(f"missing/empty input: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--manifest", required=True, type=Path)
    p.add_argument("--source-dir", required=True, type=Path)
    p.add_argument("--output-dir", required=True, type=Path)
    p.add_argument("--old-imported", required=True)
    p.add_argument("--new-imported", required=True)
    p.add_argument("files", nargs="+")
    args = p.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("acceptance") != "ACCEPTED_V06_FILE":
        raise SystemExit("producer is not an accepted whole file")
    if args.old_imported == args.new_imported:
        raise SystemExit("old/new imported identities must differ")
    records = []
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for filename in args.files:
        if Path(filename).name != filename or not filename.endswith(".v"):
            raise SystemExit(f"invalid certificate name: {filename}")
        source = args.source_dir / filename
        content = source.read_text()
        count = content.count(args.old_imported)
        if count == 0 or args.new_imported in content:
            raise SystemExit(f"unexpected imported identity in {source}")
        if filename.endswith("Correspondence.v"):
            expected = manifest.get("correspondence_source_sha256")
            if expected and digest(source) != expected:
                raise SystemExit(f"published correspondence source changed: {source}")
        output = args.output_dir / filename
        header = (
            "(** Artifact-local replay: the only source rewrite is the imported "
            "module identity.\n"
            f"    Accepted producer source SHA-256: {digest(source)}.\n"
            f"    Substitution: {args.old_imported} -> {args.new_imported}.\n"
            "    This file must be recompiled and audited by Rocq. *)\n"
        )
        output.write_text(header + content.replace(args.old_imported, args.new_imported))
        records.append({"source": str(source), "source_sha256": digest(source),
                        "output": str(output), "output_sha256": digest(output),
                        "substitutions": count})
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()
