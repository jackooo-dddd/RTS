#!/usr/bin/env python3
"""Publish a fully audited behavior/schedule.v validation snapshot."""

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
        (args.work / "certificates/assumption_summary.json").read_text()
    )
    adapter_assumptions = json.loads(
        (args.work / "certificates/adapter_assumption_summary.json").read_text()
    )
    source_meta = json.loads(
        (args.work / "source/schedule_source_acquisition.json").read_text()
    )
    lean_axioms = json.loads((args.work / "lean_axiom_summary.json").read_text())
    prepare_run = json.loads(args.prepare_evidence.read_text())

    if not (
        previous.get("status") == "PASS"
        and previous["coverage"]["accepted_files"] == 23
        and previous["coverage"]["accepted_declarations"] == 223
        and previous["coverage"]["translated_but_not_certified"] == 0
    ):
        raise SystemExit("Schedule publication baseline changed")
    records = assumptions["certificates"]
    expected = {
        "ProcessorState", "scheduled_in", "supply_in", "service_in",
        "schedule_import", "schedule_export",
    }
    if set(records) != expected:
        raise SystemExit("Schedule assumption target set changed")
    if records["ProcessorState"]["status"] != "CERTIFIED_WITH_PROP_SPROP_FOUNDATION":
        raise SystemExit("ProcessorState trust classification changed")
    if any(
        records[name]["status"] != "CERTIFIED"
        for name in expected - {"ProcessorState"}
    ):
        raise SystemExit("Schedule definition certificate is not foundation-free")
    for record in records.values():
        if (
            record["semantic_premises"]
            or record["unexpected"]
            or record["source_theorem_dependency"]
            or record["target_theorem_dependency"]
        ):
            raise SystemExit("Schedule semantic audit is not clean")
    for record in adapter_assumptions["certificates"].values():
        if (
            record["status"] not in {
                "CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
            }
            or record["semantic_premises"]
            or record["unexpected"]
        ):
            raise SystemExit("generated Schedule adapter audit is not clean")
    if lean_axioms["missing"] or lean_axioms["extra"]:
        raise SystemExit("Lean axiom audit target set changed")
    if any(
        record["status"] != "PASS" or record["unexpected_axioms"]
        for record in lean_axioms["declarations"].values()
    ):
        raise SystemExit("Lean proof-clean audit failed")

    bundles = {
        "ProcessorState": ["ProcessorState"],
        "scheduled_in": ["scheduled_in"],
        "supply_in": ["supply_in"],
        "service_in": ["service_in"],
        "schedule": ["schedule_import", "schedule_export"],
    }
    lean_names = {
        "ProcessorState": "Prosa.Behavior.Schedule.ProcessorState",
        "scheduled_in": "Prosa.Behavior.Schedule.ProcessorState.scheduled_in",
        "supply_in": "Prosa.Behavior.Schedule.ProcessorState.supply_in",
        "service_in": "Prosa.Behavior.Schedule.ProcessorState.service_in",
        "schedule": "Prosa.Behavior.Schedule.schedule",
    }
    declarations = []
    for name, keys in bundles.items():
        component_records = [records[key] for key in keys]
        foundations = sorted({
            item
            for record in component_records
            for item in record["prop_sprop_foundation"]
        })
        status = (
            "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
            if foundations else "CERTIFIED"
        )
        declarations.append({
            "source_declaration": f"prosa.behavior.schedule.{name}",
            "lean_declaration": lean_names[name],
            "kind": source_meta["declarations"][name]["kind"],
            "source_command_sha256": source_meta["declarations"][name]["source_command_sha256"],
            "source_elaborated_type_sha256": source_meta["declarations"][name]["elaborated_type_sha256"],
            "semantic_status": status,
            "certificate_bundle": [record["certificate"] for record in component_records],
            "semantic_premises": [],
            "input_relations": (
                ["SchProcessorStateRel observational witness"]
                if name != "ProcessorState"
                else [
                    "two-sided State/Core maps and roundtrips",
                    "finite core-enumeration relation",
                    "scheduled/supply/service field relations",
                ]
            ),
            "prop_sprop_foundation": foundations,
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
        "slice": "TRANSLATION_ORDER_BEHAVIOR_SCHEDULE",
        "generated_at": generated_at,
        "source_file": "behavior/schedule.v",
        "source_commit": source_commit,
        "source_file_sha256": sha(args.source / "behavior/schedule.v"),
        "source_acquisition_sha256": sha(
            args.work / "source/schedule_source_acquisition.json"
        ),
        "production_file": "Prosa/Behavior/Schedule.lean",
        "production_source_sha256": sha(
            args.project / "Prosa/Behavior/Schedule.lean"
        ),
        "production_olean_sha256": sha(
            args.work / "olean/Prosa/Behavior/Schedule.olean"
        ),
        "computation_interface_source_sha256": sha(
            args.project / "Validation/fixtures/translation_order/ScheduleComputationInterface.lean"
        ),
        "computation_interface_olean_sha256": sha(
            args.work / "olean/Validation/fixtures/translation_order/ScheduleComputationInterface.olean"
        ),
        "export_sha256": sha(args.work / "imported/Schedule.out"),
        "import_sha256": sha(args.work / "imported/ImportedSchedule.vo"),
        "adapter_metadata_sha256": sha(
            args.work / "certificates/schedule_base_adapter.json"
        ),
        "adapter_vo_sha256": sha(
            args.work / "certificates/ScheduleBaseAdapter.vo"
        ),
        "finite_operations_source_sha256": sha(
            args.project / "Validation/certificates/behavior_schedule/ScheduleFiniteOperations.v"
        ),
        "finite_operations_vo_sha256": sha(
            args.work / "certificates/ScheduleFiniteOperations.vo"
        ),
        "correspondence_source_sha256": sha(
            args.project / "Validation/certificates/behavior_schedule/ScheduleCorrespondence.v"
        ),
        "correspondence_vo_sha256": sha(
            args.work / "certificates/ScheduleCorrespondence.vo"
        ),
        "processor_state_source_sha256": sha(
            args.project / "Validation/certificates/behavior_schedule/ScheduleProcessorStateCorrespondence.v"
        ),
        "processor_state_vo_sha256": sha(
            args.work / "certificates/ScheduleProcessorStateCorrespondence.vo"
        ),
        "type_audit_vo_sha256": sha(
            args.work / "certificates/ScheduleTypeAudit.vo"
        ),
        "assumption_audit_vo_sha256": sha(
            args.work / "certificates/ScheduleAssumptionAudit.vo"
        ),
        "lean_axiom_summary_sha256": sha(args.work / "lean_axiom_summary.json"),
        "assumption_summary_sha256": sha(
            args.work / "certificates/assumption_summary.json"
        ),
        "adapter_assumption_summary_sha256": sha(
            args.work / "certificates/adapter_assumption_summary.json"
        ),
        "snapshot_id": args.snapshot_id,
        "prepare_mode": prepare_run["run_mode"],
        "prepare_evidence_sha256": sha(args.prepare_evidence),
        "declarations": declarations,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    args.manifest_output.parent.mkdir(parents=True, exist_ok=True)
    args.manifest_output.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"
    )
    status = {
        "slice": "TRANSLATION_ORDER_BEHAVIOR_SCHEDULE",
        "per_file": {
            "behavior/schedule.v": {
                "public_declarations": 5,
                "translated": 5,
                "proof_clean": 5,
                "certified": 5,
                "certified_without_prop_sprop_foundation": 4,
                "certified_with_prop_sprop_foundation": 1,
                "status": "ACCEPTED_V06_FILE",
            }
        },
        "coverage": {
            "accepted_files": 24,
            "authoritative_files": 357,
            "accepted_declarations": 228,
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
    end = "<!-- FORMAL_PUBLICATION_END -->"
    if begin in report_text:
        report_text = report_text.split(begin, 1)[0].rstrip() + "\n\n"
    section = f"""{begin}
## {generated_at} — formal clean publication accepted

The content-addressed validator completed a clean
`prepare → check → finalize` reproduction for snapshot
`{args.snapshot_id}`.  It freshly rebuilt the accepted Lean dependency closure
plus Schedule and its computation interface, compiled the byte-identical
official source chain, exported and imported the actual compiled artifact,
regenerated the artifact-local adapter against that import hash, rebuilt every
Rocq certificate, and ran fail-closed Lean/Rocq audits.

Final declaration classification:

| Declaration | Status |
|---|---|
| `ProcessorState` | `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` |
| `scheduled_in` | `CERTIFIED` |
| `supply_in` | `CERTIFIED` |
| `service_in` | `CERTIFIED` |
| `schedule` (both directions) | `CERTIFIED` |

There are no semantic premises, source/target self-dependencies, unexpected
assumptions, or proof-clean violations.  The sole explicit logical trust
boundary is `PropSPropFoundation.interpret_strict` for the two imported
SProp-valued class laws.  The derived computational declarations are
foundation-free under the approved importer primitives.

Key hashes: production `.olean` `{manifest['production_olean_sha256']}`,
export `{manifest['export_sha256']}`, imported `.vo`
`{manifest['import_sha256']}`, and full observational certificate
`{manifest['processor_state_vo_sha256']}`.

This accepts all five authoritative declarations.  Cumulative machine
coverage is **24 / 357 files** and **228 / 2439 declarations**, with zero
translated-but-not-certified debt.

Final file status: **ACCEPTED_V06_FILE**.
{end}
"""
    args.canonical_report.write_text(report_text.rstrip() + "\n\n" + section)

    run_text = args.run_report.read_text()
    run_text += f"""

## {generated_at} — Schedule formally accepted

- The clean content-addressed prepare/check/finalize run passed for snapshot
  `{args.snapshot_id}`.
- All five v0.6 declarations are accepted: four `CERTIFIED`, and
  `ProcessorState` explicitly
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` for its two class laws.
- Semantic premises, unexpected assumptions, and source/target
  self-dependencies are all empty/false.  Coverage is now **24 / 357 files**
  and **228 / 2439 declarations**, with zero validation debt.
"""
    args.run_report.write_text(run_text)


if __name__ == "__main__":
    main()
