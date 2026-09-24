#!/usr/bin/env python3
"""Replay the kernel-proved interval-operation pattern for an imported artifact.

This generates proof scripts, never assumptions. The generated files must be
compiled and individually assumption-audited against the named actual import.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


def sha(path: Path) -> str:
    if not path.is_file() or not path.stat().st_size:
        raise SystemExit(f"missing or empty input: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-nat", type=Path, required=True)
    parser.add_argument("--source-interval", type=Path, required=True)
    parser.add_argument("--imported-artifact", type=Path, required=True)
    parser.add_argument("--output-nat", type=Path, required=True)
    parser.add_argument("--output-interval", type=Path, required=True)
    args = parser.parse_args()

    artifact_hash = sha(args.imported_artifact)
    sources = (
        (args.source_nat, args.output_nat),
        (args.source_interval, args.output_interval),
    )
    for source, output in sources:
        source_hash = sha(source)
        content = source.read_text()
        if "ImportedSupply" not in content or "SupplyBaseAdapter" not in content:
            raise SystemExit(f"not a Supply interval-pattern source: {source}")
        content = content.replace("ImportedSupply", "ImportedOverheads")
        content = content.replace("SupplyBaseAdapter", "OverheadsBaseAdapter")
        content = content.replace("SupplyNatBoolOperations", "OverheadsNatBoolOperations")
        content = content.replace("SvcBoolRel", "OvhBoolRel")
        content = content.replace("svc_coq_false_to_target", "ovh_coq_false_to_target")
        content = content.replace("svc_false_elim", "ovh_false_elim")
        content = content.replace("svc_false_ne_true", "ovh_false_ne_true")
        content = content.replace("needed by Supply", "needed by Overheads")
        if source.name == "SupplyNatBoolOperations.v":
            # The interval sum uses only 0, 1, addition, and truncated
            # subtraction. The target's compiled closure need not export
            # Bool.not or Nat.lt at all.
            begin = content.index("Definition svc_target_lt")
            end = content.index("Lemma svc_target_add_related", begin)
            content = content[:begin] + content[end:]
            begin = content.index("Lemma svc_target_lt_related")
            end = content.index("Lemma svc_target_sub_succ", begin)
            content = content[:begin] + content[end:]
            content = content.replace("Print Assumptions svc_decide_lt_related.\n", "")
            content = content.replace("Print Assumptions svc_bool_not_related.\n", "")
        if source.name == "SupplyIntervalOperations.v":
            # The accepted Supply file was itself a generated replay of the
            # Service pattern. Keep a single, accurate provenance header.
            start = content.find("From mathcomp Require Import")
            if start < 0:
                raise SystemExit("missing Rocq import block")
            content = content[start:]
        header = (
            "(** GENERATED artifact-local proof replay; not an axiom.\n"
            f"    source certificate SHA-256: {source_hash}\n"
            f"    imported artifact SHA-256: {artifact_hash}\n"
            "    Substitutions: Supply import/adapter identities only.\n"
            "    Must pass Rocq compilation and Print Assumptions audit. *)\n"
        )
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(header + content)
        print(f"{output}: {sha(output)}")


if __name__ == "__main__":
    main()
