#!/usr/bin/env python3
"""Compose already audited Service/ArrivalSequence export interfaces."""

import json
from pathlib import Path


project = Path(__file__).resolve().parents[2]
tooling = project / "Validation/tooling"
service = json.loads((tooling / "behavior_service_export_config.json").read_text())
arrival = json.loads((tooling / "behavior_arrival_sequence_export_config.json").read_text())
target = "Prosa.Analysis.Definitions.CompletionSequence.completion_sequence"


def unique(items):
    return list(dict.fromkeys(items))


normalization = {
    key: unique(service["normalization"][key] + arrival["normalization"][key])
    for key in ("theorem_types", "subexpression_heads", "definition_bodies", "body_projections")
}
if normalization["theorem_types"] or normalization["subexpression_heads"] or normalization["definition_bodies"]:
    raise SystemExit("unexpected new normalization mode in accepted base config")
config = {
    "schema_version": 1,
    "module": "Validation.fixtures.translation_order.CompletionSequenceExportInterface",
    "targets": unique([target] + service["targets"] + arrival["targets"]),
    "statement_only": unique(service["statement_only"] + arrival["statement_only"]),
    "body_theorems": unique(service["body_theorems"] + arrival["body_theorems"]),
    "definition_targets": unique([target] + service["definition_targets"] + arrival["definition_targets"]),
    "normalization": normalization,
    "kernel_guard_artifacts": unique(service.get("kernel_guard_artifacts", [])
                                     + arrival.get("kernel_guard_artifacts", [])),
}
if target not in config["definition_targets"] or config["statement_only"]:
    raise SystemExit("completion-sequence target was weakened to statement-only")
output = tooling / "analysis_completion_sequence_combined_export_config.json"
output.write_text(json.dumps(config, indent=2) + "\n")
print(output)
