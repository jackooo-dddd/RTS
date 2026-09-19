#!/usr/bin/env python3
"""Record or verify exact source -> Lean export -> imported .vo provenance."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def snapshot(paths: list[Path]) -> list[dict[str, str]]:
    result = []
    for path in paths:
        resolved = path.resolve()
        if not resolved.is_file():
            raise SystemExit(f"missing provenance input: {resolved}")
        result.append({"path": str(resolved), "sha256": digest(resolved)})
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["record", "verify"])
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--source", action="append", default=[], type=Path)
    parser.add_argument("--artifact", action="append", default=[], type=Path)
    parser.add_argument("--imported", action="append", default=[], type=Path)
    args = parser.parse_args()

    current = {
        "sources": snapshot(args.source),
        "artifacts": snapshot(args.artifact),
        "imported_objects": snapshot(args.imported),
    }
    if args.mode == "record":
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(json.dumps(current, indent=2, sort_keys=True) + "\n")
        print(f"PROVENANCE_RECORDED {args.manifest}")
        return

    if not args.manifest.is_file():
        raise SystemExit("STALE_REJECTED: provenance manifest missing")
    expected = json.loads(args.manifest.read_text())
    if current != expected:
        for group in current:
            if current[group] != expected.get(group):
                print(f"STALE_REJECTED: {group} hash/path mismatch")
        raise SystemExit(1)
    print("PROVENANCE_VERIFIED: source, export artifact, and imported object hashes match")


if __name__ == "__main__":
    main()
