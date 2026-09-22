#!/usr/bin/env python3
"""Instantiate the audited ArrivalSequence certificate DAG for an artifact."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--source-dir", required=True, type=Path)
    p.add_argument("--output-dir", required=True, type=Path)
    p.add_argument("--imported-module", required=True)
    p.add_argument("--imported-artifact", required=True, type=Path)
    p.add_argument("--metadata", required=True, type=Path)
    p.add_argument(
        "--correspondence-lemma",
        action="append",
        default=[],
        help=("emit only this named correspondence lemma (repeatable); "
              "operations are still instantiated in full"),
    )
    args = p.parse_args()
    if not args.imported_artifact.is_file():
        raise SystemExit("imported artifact is missing")

    modules = {
        "ArrivalSequenceOperations": "ReadyArrivalOperations",
        "ArrivalSequenceCorrespondence": "ReadyArrivalCorrespondence",
    }
    replacements = {
        "ImportedArrivalSequence": args.imported_module,
        "ArrivalSequenceBaseAdapter": "ReadyArrivalBaseAdapter",
        **modules,
    }
    args.output_dir.mkdir(parents=True, exist_ok=True)
    generated = {}
    for source_name, output_name in modules.items():
        source = args.source_dir / f"{source_name}.v"
        text = source.read_text()
        if source_name == "ArrivalSequenceCorrespondence" and args.correspondence_lemma:
            first = re.search(r"(?m)^Lemma ", text)
            if first is None:
                raise SystemExit("Arrival correspondence source has no lemmas")
            pieces = [text[:first.start()].rstrip(), ""]
            for lemma in args.correspondence_lemma:
                match = re.search(
                    rf"(?ms)^Lemma {re.escape(lemma)}\b.*?(?=^Lemma |^Print Assumptions|\Z)",
                    text,
                )
                if match is None:
                    raise SystemExit(f"correspondence lemma not found: {lemma}")
                pieces.extend([match.group(0).rstrip(), ""])
            pieces.extend(
                f"Print Assumptions {lemma}." for lemma in args.correspondence_lemma
            )
            text = "\n".join(pieces) + "\n"
        for old, new in replacements.items():
            text = text.replace(old, new)
        output = args.output_dir / f"{output_name}.v"
        output.write_text(
            "(** GENERATED ARTIFACT-LOCAL INSTANTIATION.\n"
            f"    source: {source}\n"
            f"    source-sha256: {sha(source)}\n"
            f"    imported-artifact-sha256: {sha(args.imported_artifact)} *)\n"
            + text
        )
        generated[output_name] = {
            "source": str(source), "source_sha256": sha(source),
            "output": str(output), "output_sha256": sha(output),
        }
    args.metadata.write_text(json.dumps({
        "schema_version": 1,
        "method": "kernel_rechecked_artifact_local_module_instantiation",
        "imported_module": args.imported_module,
        "imported_artifact": str(args.imported_artifact),
        "imported_artifact_sha256": sha(args.imported_artifact),
        "correspondence_lemmas": args.correspondence_lemma or "ALL",
        "generated": generated,
    }, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
