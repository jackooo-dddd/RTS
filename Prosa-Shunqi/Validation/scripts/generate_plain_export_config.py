#!/usr/bin/env python3
"""Exact plain-SBF definitions and theorem statement over accepted Pred export."""

import json
from pathlib import Path

project = Path(__file__).resolve().parents[2]
tooling = project / "Validation/tooling"
base = json.loads((tooling / "analysis_sbf_pred_export_config.json").read_text())
prefix = "Prosa.Analysis.Definitions.Sbf.Plain."
definitions = [prefix + "supply_bound_function_respected",
               prefix + "valid_supply_bound_function"]
theorem = prefix + "sbf_respected_simplified"


def unique(values):
    return list(dict.fromkeys(values))


result = dict(base)
result["module"] = "Validation.fixtures.translation_order.PlainExportInterface"
result["targets"] = unique(definitions + [theorem] + base["targets"])
result["definition_targets"] = unique(definitions + base["definition_targets"])
result["statement_only"] = unique([theorem] + base["statement_only"])
result["body_theorems"] = base["body_theorems"]
output = tooling / "analysis_sbf_plain_export_config.json"
output.write_text(json.dumps(result, indent=2) + "\n")
print(output)
