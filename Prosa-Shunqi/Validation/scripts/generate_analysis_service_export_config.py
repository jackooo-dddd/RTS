#!/usr/bin/env python3
"""Compose exact analysis-Service bodies with accepted Service/Arrival interfaces."""

import json
from pathlib import Path

project = Path(__file__).resolve().parents[2]
tooling = project / "Validation/tooling"
service = json.loads((tooling / "behavior_service_export_config.json").read_text())
arrival = json.loads((tooling / "behavior_arrival_sequence_export_config.json").read_text())
target = [
    "Prosa.Analysis.Definitions.Service.served_jobs_at",
    "Prosa.Analysis.Definitions.Service.served_job_at",
]


def unique(items):
    return list(dict.fromkeys(items))


normalization = {
    key: unique(service["normalization"][key] + arrival["normalization"][key])
    for key in ("theorem_types", "subexpression_heads", "definition_bodies", "body_projections")
}
if any(normalization[key] for key in ("theorem_types", "subexpression_heads", "definition_bodies")):
    raise SystemExit("unexpected new normalization in accepted input")
if normalization["body_projections"] and not service.get("kernel_guard_artifacts"):
    raise SystemExit("accepted Service body projections lack kernel guards")
result = {
    "schema_version": 1,
    "module": "Validation.fixtures.translation_order.AnalysisServiceExportInterface",
    "targets": unique(target + service["targets"] + arrival["targets"]),
    "statement_only": unique(service["statement_only"] + arrival["statement_only"]),
    "body_theorems": unique(service["body_theorems"] + arrival["body_theorems"]),
    "definition_targets": unique(target + service["definition_targets"] + arrival["definition_targets"]),
    "normalization": normalization,
    "kernel_guard_artifacts": unique(service.get("kernel_guard_artifacts", [])
                                     + arrival.get("kernel_guard_artifacts", [])),
}
if result["statement_only"]:
    raise SystemExit("analysis Service must not import statement-only dependencies")
output = tooling / "analysis_definitions_service_export_config.json"
output.write_text(json.dumps(result, indent=2) + "\n")
print(output)
