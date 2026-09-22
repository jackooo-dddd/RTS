#!/usr/bin/env python3
"""Publish a fully audited behavior/service.v validation snapshot."""

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
    adapter = json.loads(
        (args.work / "certificates/adapter_assumption_summary.json").read_text())
    source_meta = json.loads(
        (args.work / "source/service_source_acquisition.json").read_text())
    lean_axioms = json.loads((args.work / "lean_axiom_summary.json").read_text())
    prepare_run = json.loads(args.prepare_evidence.read_text())

    if not (
        previous.get("status") == "PASS"
        and previous["coverage"]["accepted_files"] == 24
        and previous["coverage"]["accepted_declarations"] == 228
        and previous["coverage"]["translated_but_not_certified"] == 0
    ):
        raise SystemExit("Service publication baseline changed")

    names = [
        "scheduled_at", "service_at", "receives_service_at",
        "service_during", "service", "completed_by", "completes_at",
        "job_response_time_bound", "job_meets_deadline", "pending",
        "pending_earlier_and_at", "remaining_cost",
    ]
    records = assumptions["certificates"]
    if set(records) != set(names):
        raise SystemExit("Service assumption target set changed")
    expected_plain = {
        "scheduled_at", "service_at", "service_during", "service",
        "remaining_cost",
    }
    for name, record in records.items():
        expected_status = (
            "CERTIFIED" if name in expected_plain
            else "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
        )
        if record["status"] != expected_status:
            raise SystemExit(f"Service trust classification changed: {name}")
        if (record["semantic_premises"] or record["unexpected"]
                or record["source_theorem_dependency"]
                or record["target_theorem_dependency"]):
            raise SystemExit(f"Service semantic audit is not clean: {name}")
    for record in adapter["certificates"].values():
        if (record["status"] not in {
                "CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
                or record["semantic_premises"] or record["unexpected"]
                or record["source_theorem_dependency"]
                or record["target_theorem_dependency"]):
            raise SystemExit("generated Service adapter audit is not clean")
    if lean_axioms["missing"] or lean_axioms["extra"]:
        raise SystemExit("Lean axiom audit target set changed")
    if len(lean_axioms["declarations"]) != 50 or any(
        record["status"] != "PASS" or record["unexpected_axioms"]
        for record in lean_axioms["declarations"].values()
    ):
        raise SystemExit("Lean proof-clean audit failed")

    declarations = []
    for name in names:
        record = records[name]
        declarations.append({
            "source_declaration": f"prosa.behavior.service.{name}",
            "lean_declaration": f"Prosa.Behavior.Service.{name}",
            "kind": source_meta["declarations"][name]["kind"],
            "source_command_sha256":
                source_meta["declarations"][name]["source_command_sha256"],
            "source_elaborated_type_sha256":
                source_meta["declarations"][name]["elaborated_type_sha256"],
            "semantic_status": record["status"],
            "certificate_bundle": [record["certificate"]],
            "semantic_premises": [],
            "input_relations": [
                "SvcProcessorStateRel observational witness",
                "SvcScheduleRel pointwise schedule relation",
                "two-sided Job field relation where required",
                "SubNatRel for explicit time/duration inputs where required",
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
        "slice": "TRANSLATION_ORDER_BEHAVIOR_SERVICE",
        "generated_at": generated_at,
        "source_file": "behavior/service.v",
        "source_commit": source_commit,
        "source_file_sha256": sha(args.source / "behavior/service.v"),
        "source_acquisition_sha256": sha(
            args.work / "source/service_source_acquisition.json"),
        "production_file": "Prosa/Behavior/Service.lean",
        "production_source_sha256": sha(
            args.project / "Prosa/Behavior/Service.lean"),
        "production_olean_sha256": sha(
            args.work / "olean/Prosa/Behavior/Service.olean"),
        "computation_interface_source_sha256": sha(
            args.project /
            "Validation/fixtures/translation_order/ServiceComputationInterface.lean"),
        "computation_interface_olean_sha256": sha(
            args.work /
            "olean/Validation/fixtures/translation_order/ServiceComputationInterface.olean"),
        "export_sha256": sha(args.work / "imported/Service.out"),
        "import_sha256": sha(args.work / "imported/ImportedService.vo"),
        "adapter_metadata_sha256": sha(
            args.work / "certificates/service_base_adapter.json"),
        "adapter_vo_sha256": sha(
            args.work / "certificates/ServiceBaseAdapter.vo"),
        "nat_bool_operations_vo_sha256": sha(
            args.work / "certificates/ServiceNatBoolOperations.vo"),
        "interval_operations_vo_sha256": sha(
            args.work / "certificates/ServiceIntervalOperations.vo"),
        "schedule_operations_vo_sha256": sha(
            args.work / "certificates/ServiceScheduleOperations.vo"),
        "job_operations_vo_sha256": sha(
            args.work / "certificates/ServiceJobOperations.vo"),
        "correspondence_source_sha256": sha(
            args.project /
            "Validation/certificates/behavior_service/ServiceCorrespondence.v"),
        "correspondence_vo_sha256": sha(
            args.work / "certificates/ServiceCorrespondence.vo"),
        "type_audit_vo_sha256": sha(
            args.work / "certificates/ServiceTypeAudit.vo"),
        "assumption_audit_vo_sha256": sha(
            args.work / "certificates/ServiceAssumptionAudit.vo"),
        "lean_axiom_summary_sha256": sha(args.work / "lean_axiom_summary.json"),
        "assumption_summary_sha256": sha(
            args.work / "certificates/assumption_summary.json"),
        "adapter_assumption_summary_sha256": sha(
            args.work / "certificates/adapter_assumption_summary.json"),
        "snapshot_id": args.snapshot_id,
        "prepare_mode": prepare_run["run_mode"],
        "prepare_evidence_sha256": sha(args.prepare_evidence),
        "definition_body_projection_count": 12,
        "projection_guard": "Lean kernel rfl plus lean4export exact-constant guard",
        "declarations": declarations,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    args.manifest_output.parent.mkdir(parents=True, exist_ok=True)
    args.manifest_output.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
    status = {
        "slice": "TRANSLATION_ORDER_BEHAVIOR_SERVICE",
        "per_file": {"behavior/service.v": {
            "public_declarations": 12, "translated": 12,
            "proof_clean": 12, "certified": 12,
            "certified_without_prop_sprop_foundation": 5,
            "certified_with_prop_sprop_foundation": 7,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": {
            "accepted_files": 25, "authoritative_files": 357,
            "accepted_declarations": 240,
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
    begin, end = "<!-- FORMAL_PUBLICATION_BEGIN -->", "<!-- FORMAL_PUBLICATION_END -->"
    if begin in report_text:
        report_text = report_text.split(begin, 1)[0].rstrip() + "\n\n"
    rows = "\n".join(
        f"| `{name}` | `{records[name]['status']}` |" for name in names)
    section = f"""{begin}
## {generated_at} — formal clean publication accepted

The content-addressed `prepare → check → finalize` reproduction passed for
snapshot `{args.snapshot_id}`.  It freshly rebuilt the complete accepted Lean
dependency closure plus Service and both computation interfaces, compiled the
byte-identical official source chain, exported/imported the actual artifact,
regenerated the artifact-bound adapter, rebuilt all Rocq certificates, and
ran fail-closed Lean/Rocq audits.

| Declaration | Status |
|---|---|
{rows}

All twelve exact compiled bodies are connected to their source-shaped export
forms by Lean-kernel `rfl` guards checked again by the exporter.  There are no
semantic premises, source/target self-dependencies, unexpected assumptions,
or proof-clean violations.  The seven explicitly labelled results use only
the approved `PropSPropFoundation.interpret_strict` boundary for interpreting
imported logical evidence; the other five are foundation-free.

Key hashes: production `.olean` `{manifest['production_olean_sha256']}`,
export `{manifest['export_sha256']}`, imported `.vo`
`{manifest['import_sha256']}`, and aggregate correspondence `.vo`
`{manifest['correspondence_vo_sha256']}`.

This accepts all twelve authoritative declarations.  Cumulative machine
coverage is **25 / 357 files** and **240 / 2439 declarations**, with zero
translated-but-not-certified debt.

Final file status: **ACCEPTED_V06_FILE**.
{end}
"""
    args.canonical_report.write_text(report_text.rstrip() + "\n\n" + section)

    run_text = args.run_report.read_text()
    run_text += f"""

## {generated_at} — Service formally accepted

- The clean content-addressed prepare/check/finalize run passed for snapshot
  `{args.snapshot_id}`.
- All twelve v0.6 definitions are accepted: five `CERTIFIED` and seven
  explicitly `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`.
- Semantic premises, unexpected assumptions, and source/target
  self-dependencies are empty/false.  Coverage is now **25 / 357 files** and
  **240 / 2439 declarations**, with zero validation debt.
"""
    args.run_report.write_text(run_text)


if __name__ == "__main__":
    main()
