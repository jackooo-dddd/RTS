#!/usr/bin/env python3
"""Compose periodic target definitions with accepted Supply/DivMod interfaces."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[2]
TOOLING = PROJECT / "Validation/tooling"
BASE = TOOLING / "model_processor_supply_export_config.json"
DIVMOD = TOOLING / "div_mod_export_config.json"
OUTPUT = TOOLING / "analysis_sbf_periodic_export_config.json"
PREFIX = "Prosa.Analysis.Definitions.Sbf.Periodic."


def unique(items: list[str]) -> list[str]:
    return list(dict.fromkeys(items))


def main() -> None:
    base = json.loads(BASE.read_text())
    divmod = json.loads(DIVMOD.read_text())
    assert base["module"] == "Validation.fixtures.translation_order.SupplyComputationInterface"
    assert not base["statement_only"]
    definitions = [PREFIX + name for name in ("periodic_resource_model", "prm_sbf")]
    result = dict(base)
    result["module"] = "Validation.fixtures.translation_order.PeriodicExportInterface"
    divmod_computation = unique(divmod["definition_targets"] + divmod["body_theorems"])
    result["targets"] = unique(definitions + base["targets"] + divmod_computation)
    result["definition_targets"] = unique(definitions + base["definition_targets"]
                                          + divmod["definition_targets"])
    result["body_theorems"] = unique(base["body_theorems"] + divmod["body_theorems"])
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"config_sha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),
                      "target_count": len(result["targets"]),
                      "definition_count": len(result["definition_targets"])}, indent=2))


if __name__ == "__main__":
    main()
