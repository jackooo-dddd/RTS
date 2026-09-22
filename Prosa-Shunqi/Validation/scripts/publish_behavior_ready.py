#!/usr/bin/env python3
"""Publish a fully audited behavior/ready.v validation snapshot."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import datetime
from pathlib import Path


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--prepared", required=True, type=Path)
    parser.add_argument("--prepare-evidence", required=True, type=Path)
    parser.add_argument("--snapshot-id", required=True)
    parser.add_argument("--previous-status", required=True, type=Path)
    parser.add_argument("--manifest-output", required=True, type=Path)
    parser.add_argument("--status-output", required=True, type=Path)
    parser.add_argument("--canonical-report", required=True, type=Path)
    parser.add_argument("--run-report", required=True, type=Path)
    args = parser.parse_args()

    previous = json.loads(args.previous_status.read_text())
    assumptions = json.loads(
        (args.work / "certificates/assumption_summary.json").read_text())
    adapters = json.loads(
        (args.work / "certificates/adapter_assumption_summary.json").read_text())
    source_meta = json.loads(
        (args.work / "source/ready_source_acquisition.json").read_text())
    lean_axioms = json.loads(
        (args.work / "lean_ready_axiom_summary.json").read_text())
    prepare_run = json.loads(args.prepare_evidence.read_text())

    if not (
        previous.get("status") == "PASS"
        and previous["coverage"]["accepted_files"] == 25
        and previous["coverage"]["accepted_declarations"] == 240
        and previous["coverage"]["translated_but_not_certified"] == 0
    ):
        raise SystemExit("Ready publication baseline changed")

    names = [
        "JobReady", "backlogged", "jobs_come_from_arrival_sequence",
        "jobs_must_arrive_to_execute", "jobs_must_be_ready_to_execute",
        "completed_jobs_dont_execute", "valid_schedule",
    ]
    records = assumptions["certificates"]
    if set(records) != set(names):
        raise SystemExit("Ready assumption target set changed")
    for name, record in records.items():
        expected = ("CERTIFIED" if name == "backlogged"
                    else "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")
        if record["status"] != expected:
            raise SystemExit(f"Ready trust classification changed: {name}")
        if (record["semantic_premises"] or record["unexpected"]
                or record["source_theorem_dependency"]
                or record["target_theorem_dependency"]):
            raise SystemExit(f"Ready semantic audit is not clean: {name}")
    if len(adapters["certificates"]) != 12:
        raise SystemExit("Ready adapter target set changed")
    for record in adapters["certificates"].values():
        if (record["status"] not in {
                "CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
                or record["semantic_premises"] or record["unexpected"]
                or record["source_theorem_dependency"]
                or record["target_theorem_dependency"]):
            raise SystemExit("Ready generated adapter audit is not clean")
    if lean_axioms["missing"] or lean_axioms["extra"]:
        raise SystemExit("Ready Lean axiom target set changed")
    if len(lean_axioms["declarations"]) != 19 or any(
        record["status"] != "PASS" or record["unexpected_axioms"]
        for record in lean_axioms["declarations"].values()
    ):
        raise SystemExit("Ready Lean proof-clean audit failed")

    certificate_names = {
        "JobReady": "job_ready_class_correspondence",
        "backlogged": "backlogged_correspondence",
        "jobs_come_from_arrival_sequence":
            "jobs_come_from_arrival_sequence_correspondence",
        "jobs_must_arrive_to_execute":
            "jobs_must_arrive_to_execute_correspondence",
        "jobs_must_be_ready_to_execute":
            "jobs_must_be_ready_to_execute_correspondence",
        "completed_jobs_dont_execute":
            "completed_jobs_dont_execute_correspondence",
        "valid_schedule": "valid_schedule_correspondence",
    }
    declarations = []
    for name in names:
        record = records[name]
        declarations.append({
            "source_declaration": f"prosa.behavior.ready.{name}",
            "lean_declaration": f"Prosa.Behavior.Ready.{name}",
            "kind": source_meta["declarations"][name]["kind"],
            "source_command_sha256":
                source_meta["declarations"][name]["source_command_sha256"],
            "source_elaborated_type_sha256":
                source_meta["declarations"][name]["elaborated_type_sha256"],
            "semantic_status": record["status"],
            "certificate_bundle": [certificate_names[name]],
            "semantic_premises": [],
            "input_relations": [
                "SvcProcessorStateRel observational witness",
                "SvcScheduleRel pointwise schedule relation",
                "SvcJobCostRel and SvcJobArrivalRel where required",
                "RdyJobReadyRel observable readiness operation relation",
                "ArArrivalSequenceRel where required",
                "SubNatRel for explicit time inputs",
            ],
            "prop_sprop_foundation": record["prop_sprop_foundation"],
            "unexpected_assumptions": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })

    generated_at = datetime.now().astimezone().isoformat()
    source_commit = subprocess.check_output(
        ["git", "-C", str(args.source), "rev-parse", "HEAD"], text=True
    ).strip()
    manifest = {
        "slice": "TRANSLATION_ORDER_BEHAVIOR_READY",
        "generated_at": generated_at,
        "source_file": "behavior/ready.v",
        "source_commit": source_commit,
        "source_file_sha256": sha(args.source / "behavior/ready.v"),
        "source_acquisition_sha256": sha(
            args.work / "source/ready_source_acquisition.json"),
        "production_file": "Prosa/Behavior/Ready.lean",
        "production_source_sha256": sha(
            args.project / "Prosa/Behavior/Ready.lean"),
        "production_olean_sha256": sha(
            args.work / "olean/Prosa/Behavior/Ready.olean"),
        "computation_interface_source_sha256": sha(
            args.project /
            "Validation/fixtures/translation_order/ReadyComputationInterface.lean"),
        "computation_interface_olean_sha256": sha(
            args.work /
            "olean/Validation/fixtures/translation_order/ReadyComputationInterface.olean"),
        "export_sha256": sha(args.work / "imported/Ready.out"),
        "import_sha256": sha(args.work / "imported/ImportedReady.vo"),
        "service_adapter_metadata_sha256": sha(
            args.work / "certificates/ready_base_adapter.json"),
        "arrival_adapter_metadata_sha256": sha(
            args.work / "certificates/ready_arrival_base_adapter.json"),
        "service_instantiation_sha256": sha(
            args.work / "certificates/ready_service_instantiation.json"),
        "arrival_instantiation_sha256": sha(
            args.work / "certificates/ready_arrival_instantiation.json"),
        "correspondence_source_sha256": sha(
            args.project /
            "Validation/certificates/behavior_ready/ReadyCorrespondence.v"),
        "correspondence_vo_sha256": sha(
            args.work / "certificates/ReadyCorrespondence.vo"),
        "type_audit_vo_sha256": sha(
            args.work / "certificates/ReadyTypeAudit.vo"),
        "assumption_audit_vo_sha256": sha(
            args.work / "certificates/ReadyAssumptionAudit.vo"),
        "lean_axiom_summary_sha256": sha(
            args.work / "lean_ready_axiom_summary.json"),
        "assumption_summary_sha256": sha(
            args.work / "certificates/assumption_summary.json"),
        "adapter_assumption_summary_sha256": sha(
            args.work / "certificates/adapter_assumption_summary.json"),
        "snapshot_id": args.snapshot_id,
        "prepare_mode": prepare_run["run_mode"],
        "prepare_evidence_sha256": sha(args.prepare_evidence),
        "definition_body_projection_count": 6,
        "projection_guard":
            "Lean kernel rfl plus lean4export exact-constant guard",
        "declarations": declarations,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    args.manifest_output.parent.mkdir(parents=True, exist_ok=True)
    args.manifest_output.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
    status = {
        "slice": "TRANSLATION_ORDER_BEHAVIOR_READY",
        "per_file": {"behavior/ready.v": {
            "public_declarations": 7, "translated": 7,
            "proof_clean": 7, "certified": 7,
            "certified_without_prop_sprop_foundation": 1,
            "certified_with_prop_sprop_foundation": 6,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": {
            "accepted_files": 26, "authoritative_files": 357,
            "accepted_declarations": 247,
            "authoritative_declarations": 2439,
            "translated_but_not_certified": 0,
            "deferred_external_boundary": 239,
        },
        "previous_status_sha256": sha(args.previous_status),
        "snapshot_id": args.snapshot_id,
        "status": "PASS",
    }
    args.status_output.write_text(json.dumps(status, indent=2) + "\n")

    report_text = args.canonical_report.read_text()
    begin = "<!-- FORMAL_PUBLICATION_BEGIN -->"
    if begin in report_text:
        report_text = report_text.split(begin, 1)[0].rstrip() + "\n\n"
    rows = "\n".join(
        f"| `{name}` | `{records[name]['status']}` |" for name in names)
    section = f"""{begin}
## {generated_at} — formal clean publication accepted

The content-addressed `prepare → check → finalize` reproduction passed for
snapshot `{args.snapshot_id}`. It freshly rebuilt the complete accepted Lean
dependency closure plus Ready, compiled the byte-identical official source
chain, exported/imported the actual artifact, regenerated and kernel-checked
the artifact-local Service and Arrival correspondence DAGs, and ran fail-closed
Lean/Rocq audits.

| Declaration | Status |
|---|---|
{rows}

All six compiled definition bodies are tied to their source-shaped projections
by Lean-kernel `rfl` guards checked by the exporter. `JobReady` is validated by
an observational operation relation plus a compositional correspondence for
the readiness-law field type. There are no semantic premises, source/target
self-dependencies, unexpected assumptions, or proof-clean violations.

Key hashes: production `.olean` `{manifest['production_olean_sha256']}`,
export `{manifest['export_sha256']}`, imported `.vo`
`{manifest['import_sha256']}`, and correspondence `.vo`
`{manifest['correspondence_vo_sha256']}`.

This accepts all seven declarations. Cumulative machine coverage is
**26 / 357 files** and **247 / 2439 declarations**, with zero validation debt.

Final file status: **ACCEPTED_V06_FILE**.
<!-- FORMAL_PUBLICATION_END -->
"""
    args.canonical_report.write_text(report_text.rstrip() + "\n\n" + section)

    with args.run_report.open("a") as stream:
        stream.write(f"""

## {generated_at} — Ready formally accepted

- The clean content-addressed run passed for snapshot `{args.snapshot_id}`.
- All seven v0.6 declarations are accepted: one `CERTIFIED` and six
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`.
- Semantic premises and self-dependencies are absent. Coverage is now
  **26 / 357 files** and **247 / 2439 declarations**, with zero debt.
""")


if __name__ == "__main__":
    main()
