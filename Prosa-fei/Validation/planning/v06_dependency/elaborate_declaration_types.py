#!/usr/bin/env python3
"""Generate and merge Rocq `Check @declaration` evidence for the inventory."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from pathlib import Path


def normalize(text: str) -> str:
    return " ".join(text.split())


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    generate = sub.add_parser("generate")
    generate.add_argument("--inventory", type=Path, required=True)
    generate.add_argument("--files", type=Path, required=True)
    generate.add_argument("--output", type=Path, required=True)
    merge = sub.add_parser("merge")
    merge.add_argument("--inventory", type=Path, required=True)
    merge.add_argument("--probe-output", type=Path, required=True)
    merge.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args()

    if args.command == "generate":
        declarations = list(csv.DictReader(args.inventory.open()))
        files = list(csv.DictReader(args.files.open()))
        main_modules = [row["module"] for row in sorted(files, key=lambda r: (int(r["layer"]), r["file"]))
                        if "/refinements/" not in row["file"]]
        main_declarations = [row for row in declarations if "/refinements/" not in row["source_file"]]
        lines = ['Set Warnings "-notation-overridden".', "Set Printing Width 100000."]
        lines.extend(f"Require Import {module}." for module in main_modules)
        for row in main_declarations:
            name = row["qualified_name"]
            lines.extend([
                f'Goal True. idtac "BEGIN|{name}". Abort.',
                f"Check @{name}.",
                f'Goal True. idtac "END|{name}". Abort.',
            ])
        args.output.write_text("\n".join(lines) + "\n")
        print(json.dumps({"modules": len(main_modules), "declarations": len(main_declarations)}))
        return

    rows = list(csv.DictReader(args.inventory.open()))
    output = args.probe_output.read_text(errors="replace")
    pattern = re.compile(r"(?ms)^BEGIN\|([^\n]+)\n(.*?)^END\|\1\s*$")
    evidence: dict[str, dict[str, str]] = {}
    for match in pattern.finditer(output):
        name, rendered = match.group(1), match.group(2).strip()
        normalized = normalize(rendered)
        evidence[name] = {
            "rendered_check": rendered,
            "normalized_check": normalized,
            "sha256": hashlib.sha256(normalized.encode()).hexdigest(),
        }
    for row in rows:
        item = evidence.get(row["qualified_name"])
        if item:
            row["final_type_or_type_fingerprint"] = "rocq-check-sha256:" + item["sha256"]
            row["type_evidence_status"] = "ELABORATED_ROCQ_CHECK"
        elif "/refinements/" in row["source_file"]:
            row["type_evidence_status"] = "UNRESOLVED_EXTERNAL_BUILD_BOUNDARY_COQEAL"
        else:
            row["type_evidence_status"] = "UNRESOLVED_CHECK_OUTPUT"
    with args.inventory.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader(); writer.writerows(rows)
    args.evidence.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    edge_path = args.inventory.with_name("declaration_dag_edges.csv")
    dag_path = args.inventory.with_name("declaration_dag.json")
    if edge_path.exists():
        edges = list(csv.DictReader(edge_path.open()))
        for edge in edges:
            categories = {item for item in edge["evidence_categories"].split(";") if item}
            if edge["reference_region"] == "TYPE_OR_STRUCTURE" and edge["dependent"] in evidence:
                categories.add("ELABORATED_TYPE_CONFIRMED")
            edge["evidence_categories"] = ";".join(sorted(categories))
        with edge_path.open("w", newline="") as stream:
            writer = csv.DictWriter(stream, fieldnames=list(edges[0]), lineterminator="\n")
            writer.writeheader(); writer.writerows(edges)
        if dag_path.exists():
            dag = json.loads(dag_path.read_text())
            dag["edges"] = edges
            for node in dag["nodes"]:
                node["elaborated_type_status"] = (
                    "ELABORATED_TYPE_CONFIRMED" if node["qualified_name"] in evidence
                    else "UNRESOLVED_EXTERNAL"
                )
            dag_path.write_text(json.dumps(dag, indent=2, sort_keys=True) + "\n")
    expected = sum("/refinements/" not in row["source_file"] for row in rows)
    print(json.dumps({"expected": expected, "captured": len(evidence), "missing": expected - len(evidence)}))
    if len(evidence) != expected:
        raise SystemExit("not all buildable declarations received elaborated Check evidence")


if __name__ == "__main__":
    main()
