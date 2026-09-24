#!/usr/bin/env python3
"""Bind the Rank 45 definition to the accepted Service computation interface."""

import json
from pathlib import Path

project = Path(__file__).resolve().parents[2]
tooling = project / "Validation/tooling"
base = json.loads((tooling / "behavior_service_export_config.json").read_text())
target = "Prosa.Analysis.Definitions.JobResponseTime.job_response_time_exceeds"
result = dict(base)
result["module"] = (
    "Validation.fixtures.translation_order.JobResponseTimeExportInterface"
)
result["targets"] = [target] + [x for x in base["targets"] if x != target]
result["definition_targets"] = [target] + [
    x for x in base["definition_targets"] if x != target
]
result["kernel_guard_artifacts"] = [
    "Validation/fixtures/translation_order/ServiceComputationInterface.lean"
]
path = tooling / "analysis_job_response_time_export_config.json"
path.write_text(json.dumps(result, indent=2) + "\n")
print(path)
