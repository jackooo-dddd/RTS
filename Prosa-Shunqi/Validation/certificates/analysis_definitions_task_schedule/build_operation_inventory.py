#!/usr/bin/env python3
"""Bind Rank 65's pre-freeze operation inventory to exact local evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


WORK = "Validation/.work/experiments/analysis_definitions_task_schedule"
TARGET = "Validation/certificates/analysis_definitions_task_schedule/TaskScheduleCorrespondence.v"
ARRIVAL = f"{WORK}/certificates/ArrivalSequenceOperations.v"
SERVICE_NAT = f"{WORK}/certificates/ServiceNatBoolOperations.v"
SERVICE_INTERVAL = f"{WORK}/certificates/ServiceIntervalOperations.v"
SERVICE_STATE = f"{WORK}/certificates/ServiceScheduleOperations.v"
INTERFACE = "Validation/fixtures/translation_order/TaskScheduleComputationInterface.lean"
IMPORTED = f"{WORK}/imported/ImportedTaskSchedule.vo"

DECLARATIONS = [
    ("scheduled_jobs_of_task_at", ["scheduled_jobs_at", "job_of_task", "list.filter", "bool.truth"]),
    ("task_scheduled_at", ["scheduled_jobs_of_task_at", "list.isEmpty", "bool.not"]),
    ("task_service_at", ["scheduled_jobs_of_task_at", "service_at", "list.foldr_nat_sum", "nat.add"]),
    ("task_service_during", ["task_service_at", "interval.half_open", "interval.nat_sum", "nat.sub", "nat.add"]),
    ("task_service", ["task_service_during", "nat.zero"]),
    ("served_jobs_of_task_at", ["scheduled_jobs_of_task_at", "receives_service_at", "list.filter", "bool.truth"]),
    ("task_served_at", ["served_jobs_of_task_at", "list.isEmpty", "bool.not"]),
]

# Each operation names its actual proof, not merely a similarly named source.
# The two interval projections and both isEmpty equations are kernel-guarded.
BRIDGES = {
    "scheduled_jobs_at": ([TARGET, ARRIVAL, SERVICE_STATE], ["ts_arrivals_up_to_related", "ts_scheduled_at_related", "ar_filter_related"]),
    "job_of_task": ([TARGET], ["ts_job_of_task_related", "ts_decide_eq_related"]),
    "list.filter": ([ARRIVAL, TARGET], ["ar_filter_related"]),
    "bool.truth": ([ARRIVAL, TARGET], ["ar_bool_truth_correspondence"]),
    "scheduled_jobs_of_task_at": ([TARGET], ["scheduled_jobs_of_task_at_correspondence"]),
    "list.isEmpty": ([TARGET, INTERFACE], ["ts_nil_eq_isEmpty_related", "production_isEmpty_nil", "production_isEmpty_cons"]),
    "bool.not": ([SERVICE_NAT], ["svc_bool_not_related"]),
    "service_at": ([TARGET, SERVICE_STATE], ["ts_service_at_related", "svc_service_in_related"]),
    "list.foldr_nat_sum": ([TARGET], ["ts_job_fold_related", "ts_mathcomp_big_seq_as_fold"]),
    "nat.add": ([SERVICE_NAT, TARGET], ["svc_target_add_related"]),
    "task_service_at": ([TARGET], ["task_service_at_correspondence"]),
    "interval.half_open": ([SERVICE_INTERVAL, INTERFACE], ["svc_range_related", "taskServiceDuringProjection_guard"]),
    "interval.nat_sum": ([SERVICE_INTERVAL, INTERFACE], ["svc_interval_sum_related", "taskServiceDuringProjection_guard"]),
    "nat.sub": ([SERVICE_NAT, SERVICE_INTERVAL], ["svc_target_sub_related"]),
    "task_service_during": ([TARGET, INTERFACE], ["task_service_during_correspondence", "taskServiceDuringProjection_guard"]),
    "nat.zero": ([SERVICE_NAT, TARGET], ["svc_target_zero", "task_service_correspondence"]),
    "receives_service_at": ([TARGET, SERVICE_NAT], ["ts_receives_service_at_related", "svc_decide_lt_related"]),
    "served_jobs_of_task_at": ([TARGET], ["served_jobs_of_task_at_correspondence"]),
}


def digest(path: Path) -> str:
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit(f"missing/empty evidence: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-import-sha256", required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    if digest(root / IMPORTED) != args.expected_import_sha256:
        raise SystemExit("imported artifact changed")
    used = {operation for _, operations in DECLARATIONS for operation in operations}
    if used != set(BRIDGES):
        raise SystemExit(f"operation map mismatch: {used ^ set(BRIDGES)}")

    def evidence(relative: str) -> dict[str, str]:
        return {"path": relative, "sha256": digest(root / relative)}

    snapshots = {
        "official_v06_source": "Validation/.work/prosa-v06-414e667/analysis/definitions/task_schedule.v",
        "lean_source": "Prosa/Analysis/Definitions/TaskSchedule.lean",
        "kernel_guarded_interface": INTERFACE,
        "compiled_target_olean": f"{WORK}/olean/Prosa/Analysis/Definitions/TaskSchedule.olean",
        "actual_export": f"{WORK}/imported/TaskSchedule.out",
        "actual_import": IMPORTED,
    }
    config = {
        "schema_version": 1,
        "scope": "analysis/definitions/task_schedule.v Rank65 seven-definition semantic-operation inventory",
        "inventory_refinement": "Pre-freeze list.map/list.nat_sum for task_service_at resolved to actual target List.foldr with Nat.add; interval still uses List.map over half-open range.",
        "snapshot_inputs": [evidence(path) | {"name": name} for name, path in snapshots.items()],
        "declarations": [
            {"name": name, "cluster": "task_schedule_definitions", "operations": operations}
            for name, operations in DECLARATIONS
        ],
        "certified_bridges": {
            operation: {
                "status": "CERTIFIED_WITH_PROP_SPROP_FOUNDATION",
                "binding": "ACTUAL_ARTIFACT",
                "evidence": [evidence(path) for path in paths],
                "actual_artifact_evidence": [evidence(IMPORTED)],
                "certificate_names": names,
            }
            for operation, (paths, names) in sorted(BRIDGES.items())
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(config, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
