#!/usr/bin/env python3
"""Compose exact Rank 44 interface with accepted Service computation export."""

import json
from pathlib import Path

project = Path(__file__).resolve().parents[2]
tooling = project / "Validation/tooling"
base = json.loads((tooling / "behavior_service_export_config.json").read_text())
prefix = "Prosa.Analysis.Definitions.SchedulePrefix."
definition = prefix + "identical_prefix"
theorems = [prefix + "identical_prefix_scheduled_at",
            prefix + "identical_prefix_inclusion"]


def unique(items):
    return list(dict.fromkeys(items))


scheduled_at = "Prosa.Behavior.Service.scheduled_at"
core_enum = "Prosa.Validation.ScheduleInterface.coreEnumeration"
scheduled_iff = "Prosa.Validation.ScheduleInterface.production_scheduled_in_eq_true_iff"
projection = "Prosa.Validation.ServiceInterface.scheduledAtProjection"
needed = [scheduled_at, core_enum, scheduled_iff, projection]
result = dict(base)
result["module"] = "Validation.fixtures.translation_order.SchedulePrefixExportInterface"
result["targets"] = unique([definition] + theorems + needed)
result["definition_targets"] = [definition, scheduled_at, core_enum, projection]
result["statement_only"] = theorems
result["body_theorems"] = [scheduled_iff]
result["normalization"] = {
    "theorem_types": [],
    "subexpression_heads": [],
    "definition_bodies": [],
    "body_projections": [item for item in base["normalization"]["body_projections"]
                         if item.startswith(scheduled_at + "=")],
}
result["kernel_guard_artifacts"] = [
    "Validation/fixtures/translation_order/ServiceComputationInterface.lean"
]
output = tooling / "analysis_schedule_prefix_export_config.json"
output.write_text(json.dumps(result, indent=2) + "\n")
print(output)
