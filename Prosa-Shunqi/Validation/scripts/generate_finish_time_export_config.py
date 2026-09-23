#!/usr/bin/env python3
"""Compose Rank 38's exact target export with the accepted Service interface."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
TOOLING = PROJECT / "Validation/tooling"
BASE = TOOLING / "behavior_service_export_config.json"
OUTPUT = TOOLING / "analysis_finish_time_export_config.json"
PREFIX = "Prosa.Analysis.Definitions.FinishTime."
TARGETS = ["finish_time", "finished_at_finish_time", "earliest_finish_time",
           "completes_at_finish_time", "response_time"]


def unique(items: list[str]) -> list[str]:
    return list(dict.fromkeys(items))


def main() -> None:
    base = json.loads(BASE.read_text())
    assert base["module"] == "Validation.fixtures.translation_order.ServiceComputationInterface"
    assert not base["statement_only"]
    definitions = [PREFIX + "finish_time", PREFIX + "response_time"]
    corollaries = [PREFIX + name for name in TARGETS[1:4]]
    body_theorems = ["Nat.find_spec", "Nat.find_min'"]
    result = dict(base)
    result["module"] = "Validation.fixtures.translation_order.FinishTimeExportInterface"
    result["targets"] = unique(definitions + corollaries + body_theorems + base["targets"])
    result["definition_targets"] = unique(definitions + base["definition_targets"])
    result["statement_only"] = corollaries
    result["body_theorems"] = unique(body_theorems + base["body_theorems"])
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    digest = hashlib.sha256(OUTPUT.read_bytes()).hexdigest()
    print(json.dumps({"output": str(OUTPUT), "sha256": digest,
                      "definition_count": len(result["definition_targets"]),
                      "statement_only_count": len(corollaries),
                      "body_theorem_count": len(result["body_theorems"])}, indent=2))


if __name__ == "__main__":
    main()
