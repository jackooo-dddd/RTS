#!/usr/bin/env python3
"""Compose Rank 41 definitions and exact theorem type with Supply interface."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
TOOLING = PROJECT / "Validation/tooling"
BASE = TOOLING / "model_processor_supply_export_config.json"
ARRIVAL = TOOLING / "behavior_arrival_sequence_export_config.json"
OUTPUT = TOOLING / "analysis_sbf_pred_export_config.json"
PREFIX = "Prosa.Analysis.Definitions.Sbf.Pred."
DEFINITIONS = [PREFIX + n for n in ("pred_sbf_respected", "valid_pred_sbf",
                                     "sbf_is_monotone", "unit_supply_bound_function")]
THEOREM = PREFIX + "sbf_bounded_by_duration"


def unique(items: list[str]) -> list[str]:
    return list(dict.fromkeys(items))


def main() -> None:
    base = json.loads(BASE.read_text())
    arrival = json.loads(ARRIVAL.read_text())
    assert base["module"] == "Validation.fixtures.translation_order.SupplyComputationInterface"
    assert not base["statement_only"]
    result = dict(base)
    result["module"] = "Validation.fixtures.translation_order.PredExportInterface"
    result["targets"] = unique(DEFINITIONS + [THEOREM]
                               + base["targets"] + arrival["targets"])
    result["definition_targets"] = unique(DEFINITIONS + base["definition_targets"]
                                          + arrival["definition_targets"])
    result["body_theorems"] = unique(base["body_theorems"]
                                     + arrival["body_theorems"])
    result["statement_only"] = [THEOREM]
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"config_sha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),
                      "target_count": len(result["targets"]),
                      "definition_count": len(result["definition_targets"])}, indent=2))


if __name__ == "__main__":
    main()
