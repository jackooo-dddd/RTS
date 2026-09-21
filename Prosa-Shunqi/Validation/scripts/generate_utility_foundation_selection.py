#!/usr/bin/env python3
"""Generate the authoritative selection snapshot for UTILITY_FOUNDATION_EXPANSION."""

from __future__ import annotations

import csv
import hashlib
import json
from collections import Counter
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo


TARGETS = [
    "util/nat.v",
    "util/unit_growth.v",
    "util/search_arg.v",
    "util/list.v",
    "util/sum.v",
]

ACCEPTED_BASELINE_FILES = {
    "behavior/time.v",
    "util/notation.v",
    "util/tactics.v",
    "util/rel.v",
    "util/seqset.v",
    "util/subadditivity.v",
    "util/supremum.v",
}

BOUNDARIES = {
    "util/nat.v": [
        "Rocq nat <-> Lean Nat",
        "truncated natural subtraction",
        "Nat addition and order",
    ],
    "util/unit_growth.v": [
        "higher-order Nat-function relation",
        "Nat arithmetic/order/subtraction",
        "recursive slowed computation",
        "Bool predicates and Prop quantifiers",
    ],
    "util/search_arg.v": [
        "Rocq option <-> Lean Option",
        "Bool predicate/relation preservation",
        "recursive half-open Nat-range search",
        "extremum and earliest-witness semantics",
    ],
    "util/list.v": [
        "Rocq seq <-> Lean List preserving order and multiplicity",
        "eqType <-> carrier Type + DecidableEq",
        "membership/filter/count/map/append",
        "Nat iota/range endpoint semantics",
        "recursive rem_all",
    ],
    "util/sum.v": [
        "MathComp sequence bigop preserving multiplicity",
        "MathComp Nat interval bigop with exact half-open endpoints",
        "Bool-filtered sums",
        "partitioning and reordering",
    ],
}

DIFFICULTY = {
    "util/nat.v": "LOW",
    "util/unit_growth.v": "HIGH",
    "util/search_arg.v": "HIGH",
    "util/list.v": "HIGH",
    "util/sum.v": "HIGH",
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def split_deps(value: str) -> list[str]:
    return [item for item in value.split(";") if item]


def validation_class(source_file: str, name: str, kind: str, reuse: str) -> str:
    if kind in {"Lemma", "Theorem", "Fact", "Corollary", "Remark", "Proposition"}:
        if source_file == "util/sum.v":
            return "NEW_REPRESENTATION_CERTIFICATE"
        return "THEOREM_STATEMENT_ONLY"
    if name in {"slowed", "search_arg"}:
        return "CUSTOM_SEMANTIC_VALIDATION"
    if name == "rem_all":
        return "DIRECT_REUSE_BRIDGE"
    if source_file == "util/list.v" and name in {
        "max0", "first0", "last0", "range"
    }:
        return "DIRECT_REUSE_BRIDGE"
    if source_file in {"util/list.v", "util/unit_growth.v"}:
        return "COMPOSE_EXISTING_BRIDGES"
    if reuse == "REUSE_AFTER_REVALIDATION":
        return "DIRECT_REUSE_BRIDGE"
    return "NEW_PRIMITIVE_BRIDGE"


def main() -> None:
    project = Path(__file__).resolve().parents[2]
    validation = project / "Validation"
    dependency = validation / "planning/v06_dependency"
    mapping = validation / "planning/v06_mapping"
    pipeline = validation / "planning/v06_pipeline"

    layers = {
        row["file"]: row
        for row in csv.DictReader((dependency / "file_layers.csv").open())
    }
    inventory = list(csv.DictReader((dependency / "declaration_inventory.csv").open()))
    migration = {
        (row["v06_file"], row["v06_declaration"]): row
        for row in csv.DictReader((mapping / "v06_migration_table.csv").open())
    }
    file_inventory = {
        row["file"]: row
        for row in csv.DictReader((dependency / "file_inventory.csv").open())
    }

    files = []
    total = 0
    for source_file in TARGETS:
        layer = layers[source_file]
        declarations = []
        source_rows = [row for row in inventory if row["source_file"] == source_file]
        for row in source_rows:
            mig = migration[(source_file, row["declaration_name"])]
            declarations.append({
                "source_order": int(row["source_order"]),
                "rocq_declaration": row["qualified_name"],
                "declaration_name": row["declaration_name"],
                "kind": row["kind"],
                "elaborated_type_fingerprint": row["final_type_or_type_fingerprint"],
                "dependency_confidence": mig["v06_dependency_confidence"],
                "migration_action": mig["reuse_action"],
                "lean_candidate": mig["lean_declaration"] or None,
                "lean_candidate_provenance": mig["lean_candidate_provenance"],
                "representation_policy": mig["representation_policy"],
                "review_required": mig["review_required"].lower() == "true",
                "validation_class": validation_class(
                    source_file,
                    row["declaration_name"],
                    row["kind"],
                    mig["reuse_action"],
                ),
            })
        direct_internal = split_deps(layer["direct_internal_dependencies"])
        ready = all(dep in ACCEPTED_BASELINE_FILES for dep in direct_internal)
        if source_file == "util/sum.v" and "util/nat.v" in direct_internal:
            readiness_note = "deferred until util/nat.v reaches ACCEPTED_V06_FILE"
        else:
            readiness_note = "all authoritative direct internal dependencies accepted"
        files.append({
            "source_file": source_file,
            "module": layer["module"],
            "file_layer": int(layer["layer"]),
            "source_sha256": file_inventory[source_file]["sha256"],
            "loc": int(file_inventory[source_file]["lines"]),
            "direct_internal_dependencies": direct_internal,
            "direct_external_dependencies": split_deps(layer["direct_external_dependencies"]),
            "public_declaration_count": len(declarations),
            "migration_actions": dict(Counter(d["migration_action"] for d in declarations)),
            "representation_boundaries": BOUNDARIES[source_file],
            "expected_validation_difficulty": DIFFICULTY[source_file],
            "FILE_DAG_READY_INITIAL": ready,
            "readiness_note": readiness_note,
            "declarations": declarations,
        })
        total += len(declarations)

    if total != 104:
        raise SystemExit(f"inventory mismatch: expected 104 declarations, found {total}")

    closure_status = pipeline / "foundation_slice_2_closure_status.json"
    closure_manifest = pipeline / "foundation_slice_2_closure_manifest.json"
    result = {
        "slice": "UTILITY_FOUNDATION_EXPANSION",
        "generated_at": datetime.now(ZoneInfo("Asia/Hong_Kong")).isoformat(),
        "authority": {
            "prosa_commit": "414e66760333eaa4ef78c685bcf53291c527a548",
            "lean": "4.33.1",
            "mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
            "file_dag_policy": "authoritative readiness graph",
            "declaration_dag_policy": "fine-grained ordering/context aid only",
        },
        "baseline": {
            "accepted_files": 7,
            "accepted_declarations": 24,
            "translated_not_certified": 0,
            "foundation_slice_2_closure_status_sha256": sha(closure_status),
            "foundation_slice_2_closure_manifest_sha256": sha(closure_manifest),
        },
        "selection": {
            "source_file_count": len(files),
            "public_declaration_count": total,
            "files": files,
        },
        "execution_gate": {
            "initially_ready": [
                f["source_file"] for f in files if f["FILE_DAG_READY_INITIAL"]
            ],
            "deferred_until_nat_accepted": ["util/sum.v"],
        },
    }
    out = pipeline / "utility_foundation_expansion_selection.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=False) + "\n")
    print(out)


if __name__ == "__main__":
    main()
