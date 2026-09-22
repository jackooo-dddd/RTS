#!/usr/bin/env python3
"""Regenerate and audit declaration counts in the v0.6 file execution order.

The rank sequence is an intentionally reviewed linearization.  This script does
not invent a new order: it checks the existing 357 ranks against the
authoritative file DAG/layers and fills the public-declaration column directly
from declaration_inventory.csv.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from collections import Counter
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo


PROJECT = Path(__file__).resolve().parents[2]
DEPENDENCY = PROJECT / "Validation/planning/v06_dependency"
ORDER = PROJECT / "v06_file_translation_order.md"
AUDIT = PROJECT / "Validation/planning/v06_pipeline/file_translation_order_audit.json"

ROW_RE = re.compile(r"^(\d{3})\s+L(\d{2})\s+(.+?\.v)(?:\s+(\d+))?$")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_order_rows(text: str) -> list[tuple[int, int, str]]:
    rows: list[tuple[int, int, str]] = []
    for line in text.splitlines():
        match = ROW_RE.fullmatch(line)
        if match:
            rows.append((int(match.group(1)), int(match.group(2)), match.group(3)))
    return rows


def replace_block(
    text: str,
    heading: str,
    rows: list[tuple[int, int, str]],
    counts: Counter[str],
) -> str:
    start = text.index(heading)
    fence_start = text.index("```text", start)
    body_start = text.index("\n", fence_start) + 1
    fence_end = text.index("```", body_start)
    rendered = ["Rank Layer Source file Public declarations"]
    rendered.extend(f"{rank:03d}  L{layer:02d}  {source}  {counts[source]}" for rank, layer, source in rows)
    return text[:body_start] + "\n".join(rendered) + "\n" + text[fence_end:]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="rewrite the two order tables and audit JSON")
    args = parser.parse_args()

    original = ORDER.read_text()
    rows = read_order_rows(original)
    if len(rows) != 357:
        raise SystemExit(f"expected 357 ranked files, found {len(rows)}")

    ranks = [rank for rank, _, _ in rows]
    files = [source for _, _, source in rows]
    if ranks != list(range(1, 358)):
        raise SystemExit("ranks are not exactly 1..357")
    if len(set(files)) != 357:
        raise SystemExit("duplicate source file in order")

    with (DEPENDENCY / "declaration_inventory.csv").open(newline="") as handle:
        declarations = list(csv.DictReader(handle))
    counts = Counter(row["source_file"] for row in declarations)

    dag = json.loads((DEPENDENCY / "file_dag.json").read_text())
    nodes = {node["file"]: node for node in dag["nodes"]}
    if set(files) != set(nodes):
        missing = sorted(set(nodes) - set(files))
        extra = sorted(set(files) - set(nodes))
        raise SystemExit(f"scope mismatch: missing={missing}, extra={extra}")

    rank_of = {source: rank for rank, _, source in rows}
    layer_mismatches = [
        {"file": source, "order_layer": layer, "dag_layer": nodes[source]["layer"]}
        for _, layer, source in rows
        if layer != nodes[source]["layer"]
    ]
    if layer_mismatches:
        raise SystemExit(f"layer mismatches: {layer_mismatches}")

    edge_violations = []
    for edge in dag["edges"]:
        dependency = edge["dependency_file"]
        dependent = edge["dependent_file"]
        if rank_of[dependency] >= rank_of[dependent]:
            edge_violations.append(
                {
                    "dependency": dependency,
                    "dependent": dependent,
                    "dependency_rank": rank_of[dependency],
                    "dependent_rank": rank_of[dependent],
                    "edge_types": edge["edge_types"],
                }
            )
    if edge_violations:
        raise SystemExit(f"topological violations: {edge_violations[:20]}")

    if len(declarations) != 2439 or sum(counts[source] for source in files) != 2439:
        raise SystemExit("declaration inventory does not total 2439 over the ranked scope")

    main_rows = rows[:343]
    deferred_rows = rows[343:]
    if any(nodes[source]["build_group"] != "main" for _, _, source in main_rows):
        raise SystemExit("a non-main node appears in ranks 1..343")
    if any(nodes[source]["build_group"] == "main" for _, _, source in deferred_rows):
        raise SystemExit("a main node appears in deferred ranks 344..357")

    updated = replace_block(original, "## 全部文件顺序：MAIN", main_rows, counts)
    updated = replace_block(updated, "## Deferred：refinement / CoqEAL 边界", deferred_rows, counts)
    if not args.write and updated != original:
        raise SystemExit("translation-order declaration counts are stale; rerun with --write")

    audit = {
        "generated_at": datetime.now(ZoneInfo("Asia/Hong_Kong")).isoformat(timespec="seconds"),
        "source_commit": "414e66760333eaa4ef78c685bcf53291c527a548",
        "files": len(rows),
        "main_files": len(main_rows),
        "deferred_refinement_files": len(deferred_rows),
        "public_declarations": len(declarations),
        "internal_edges_checked": len(dag["edges"]),
        "cycles": dag["cycles"],
        "topological_violations": edge_violations,
        "layer_mismatches": layer_mismatches,
        "inventory_sha256": sha256(DEPENDENCY / "declaration_inventory.csv"),
        "file_layers_sha256": sha256(DEPENDENCY / "file_layers.csv"),
        "file_dag_sha256": sha256(DEPENDENCY / "file_dag.json"),
        "result": "PASS",
    }

    if args.write:
        ORDER.write_text(updated)
        audit["translation_order_sha256"] = sha256(ORDER)
        AUDIT.write_text(json.dumps(audit, indent=2) + "\n")
    else:
        print(json.dumps(audit, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
