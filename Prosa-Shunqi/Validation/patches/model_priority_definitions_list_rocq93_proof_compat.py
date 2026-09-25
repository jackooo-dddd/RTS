#!/usr/bin/env python3
"""Make a source-interface-preserving Rocq 9.3 util/list proof-only copy.

This never changes the pinned official source.  All 48 opaque proof intervals
are replaced by `Admitted.` while declaration headers, computational bodies,
imports, names, and exports remain byte-identical.  The copy is only a source
type acquisition dependency for model/priority/definitions.v; the semantic
certificate audit must reject any dependency on these temporary axioms.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

SOURCE_SHA256 = "7bb5784dc312aef4ec80b00314a36f938a20e29ed1e7d68475b9c2dca9cada6a"
PROOF_COUNT = 48
PROOF = re.compile(rb"Proof\..*?Qed\.", re.DOTALL)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--metadata", required=True, type=Path)
    args = parser.parse_args()
    original = args.source.read_bytes()
    if sha(original) != SOURCE_SHA256:
        raise SystemExit("pinned official util/list.v hash mismatch")
    intervals = list(PROOF.finditer(original))
    if len(intervals) != PROOF_COUNT:
        raise SystemExit(f"expected {PROOF_COUNT} opaque proofs, got {len(intervals)}")
    if original.count(b"Proof.") != PROOF_COUNT or original.count(b"Qed.") != PROOF_COUNT:
        raise SystemExit("unexpected proof terminator count")
    compatibility = PROOF.sub(b"Admitted.", original)
    parts = PROOF.split(original)
    if len(parts) != PROOF_COUNT + 1 or not all(part in compatibility for part in parts if part):
        raise SystemExit("non-proof source region changed")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.metadata.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(compatibility)
    report = {
        "source_commit": "414e66760333eaa4ef78c685bcf53291c527a548",
        "source_file": "util/list.v",
        "source_sha256": SOURCE_SHA256,
        "compatibility_sha256": sha(compatibility),
        "mode": "OPAQUE_PROOF_BODY_ONLY_REPLACEMENT",
        "proof_interval_count": PROOF_COUNT,
        "proof_interval_sha256": [sha(m.group()) for m in intervals],
        "nonproof_region_sha256": sha(b"".join(parts)),
        "semantic_use": "source type acquisition only; no theorem proof from this copy may be a final certificate assumption",
    }
    args.metadata.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
