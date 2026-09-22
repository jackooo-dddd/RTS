#!/usr/bin/env python3
"""Publish a fully audited model/processor/supply.v snapshot."""

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
    p = argparse.ArgumentParser()
    p.add_argument("--project", required=True, type=Path)
    p.add_argument("--source", required=True, type=Path)
    p.add_argument("--work", required=True, type=Path)
    p.add_argument("--prepare-evidence", required=True, type=Path)
    p.add_argument("--snapshot-id", required=True)
    p.add_argument("--previous-status", required=True, type=Path)
    p.add_argument("--manifest-output", required=True, type=Path)
    p.add_argument("--status-output", required=True, type=Path)
    p.add_argument("--canonical-report", required=True, type=Path)
    p.add_argument("--run-report", required=True, type=Path)
    args = p.parse_args()

    previous = json.loads(args.previous_status.read_text())
    assumptions = json.loads(
        (args.work / "certificates/assumption_summary.json").read_text())
    adapters = json.loads(
        (args.work / "certificates/adapter_assumption_summary.json").read_text())
    source_meta = json.loads(
        (args.work / "source/supply_source_acquisition.json").read_text())
    lean_axioms = json.loads((args.work / "lean_axiom_summary.json").read_text())
    prepare_run = json.loads(args.prepare_evidence.read_text())

    if not (
        previous.get("status") == "PASS"
        and previous["coverage"]["accepted_files"] == 27
        and previous["coverage"]["accepted_declarations"] == 247
        and previous["coverage"]["translated_but_not_certified"] == 0
    ):
        raise SystemExit("Supply publication baseline changed")

    names = [
        "supply_at", "supply_during", "has_supply", "is_blackout",
        "blackout_during",
    ]
    records = assumptions["certificates"]
    if set(records) != set(names + ["supply_bool_to_nat"]):
        raise SystemExit("Supply assumption target set changed")
    plain = {"supply_at", "supply_during"}
    for name in names:
        record = records[name]
        expected = (
            "CERTIFIED" if name in plain
            else "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
        )
        if record["status"] != expected:
            raise SystemExit(f"Supply trust classification changed: {name}")
        if (record["semantic_premises"] or record["unexpected"]
                or record["source_theorem_dependency"]
                or record["target_theorem_dependency"]):
            raise SystemExit(f"Supply semantic audit is not clean: {name}")
    helper = records["supply_bool_to_nat"]
    if (helper["status"] != "CERTIFIED" or helper["semantic_premises"]
            or helper["unexpected"]):
        raise SystemExit("Bool-to-Nat bridge audit is not clean")
    for record in adapters["certificates"].values():
        if (record["status"] not in {
                "CERTIFIED", "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"}
                or record["semantic_premises"] or record["unexpected"]
                or record["source_theorem_dependency"]
                or record["target_theorem_dependency"]):
            raise SystemExit("Supply adapter audit is not clean")
    if lean_axioms["missing"] or lean_axioms["extra"]:
        raise SystemExit("Lean axiom target set changed")
    if len(lean_axioms["declarations"]) != 17 or any(
        r["status"] != "PASS" or r["unexpected_axioms"]
        for r in lean_axioms["declarations"].values()
    ):
        raise SystemExit("Lean proof-clean audit failed")

    declarations = []
    for name in names:
        record = records[name]
        declarations.append({
            "source_declaration": f"prosa.model.processor.supply.{name}",
            "lean_declaration": f"Prosa.Model.Processor.Supply.{name}",
            "kind": source_meta["declarations"][name]["kind"],
            "source_command_sha256":
                source_meta["declarations"][name]["source_command_sha256"],
            "source_elaborated_type_sha256":
                source_meta["declarations"][name]["elaborated_type_sha256"],
            "semantic_status": record["status"],
            "certificate_bundle": [record["certificate"]],
            "semantic_premises": [],
            "input_relations": [
                "SupplyProcessorStateRel supply-only observational witness",
                "SupplyScheduleRel pointwise schedule relation",
                "SubNatRel for explicit interval/time inputs",
            ],
            "prop_sprop_foundation": record["prop_sprop_foundation"],
            "unexpected_assumptions": [],
            "source_theorem_dependency": False,
            "target_theorem_dependency": False,
            "acceptance": "ACCEPTED_V06_TRANSLATION",
        })

    generated_at = datetime.now().astimezone().isoformat()
    manifest = {
        "slice": "TRANSLATION_ORDER_MODEL_PROCESSOR_SUPPLY",
        "generated_at": generated_at,
        "source_file": "model/processor/supply.v",
        "source_commit": subprocess.check_output(
            ["git", "-C", str(args.source), "rev-parse", "HEAD"], text=True
        ).strip(),
        "source_file_sha256": sha(args.source / "model/processor/supply.v"),
        "source_acquisition_sha256": sha(
            args.work / "source/supply_source_acquisition.json"),
        "production_file": "Prosa/Model/Processor/Supply.lean",
        "production_source_sha256": sha(
            args.project / "Prosa/Model/Processor/Supply.lean"),
        "production_olean_sha256": sha(
            args.work / "olean/Prosa/Model/Processor/Supply.olean"),
        "computation_interface_source_sha256": sha(
            args.project / "Validation/fixtures/translation_order/SupplyComputationInterface.lean"),
        "computation_interface_olean_sha256": sha(
            args.work / "olean/Validation/fixtures/translation_order/SupplyComputationInterface.olean"),
        "export_sha256": sha(args.work / "imported/Supply.out"),
        "import_sha256": sha(args.work / "imported/ImportedSupply.vo"),
        "schedule_adapter_metadata_sha256": sha(
            args.work / "certificates/supply_schedule_base_adapter.json"),
        "supply_adapter_metadata_sha256": sha(
            args.work / "certificates/supply_base_adapter.json"),
        "schedule_instantiation_sha256": sha(
            args.work / "certificates/supply_schedule_instantiation.json"),
        "interval_instantiation_sha256": sha(
            args.work / "certificates/supply_interval_instantiation.json"),
        "correspondence_source_sha256": sha(
            args.project / "Validation/certificates/model_processor_supply/SupplyCorrespondence.v"),
        "correspondence_vo_sha256": sha(
            args.work / "certificates/SupplyCorrespondence.vo"),
        "type_audit_vo_sha256": sha(
            args.work / "certificates/SupplyTypeAudit.vo"),
        "assumption_audit_vo_sha256": sha(
            args.work / "certificates/SupplyAssumptionAudit.vo"),
        "lean_axiom_summary_sha256": sha(args.work / "lean_axiom_summary.json"),
        "assumption_summary_sha256": sha(
            args.work / "certificates/assumption_summary.json"),
        "adapter_assumption_summary_sha256": sha(
            args.work / "certificates/adapter_assumption_summary.json"),
        "snapshot_id": args.snapshot_id,
        "prepare_mode": prepare_run["run_mode"],
        "prepare_evidence_sha256": sha(args.prepare_evidence),
        "definition_body_projection_count": 5,
        "projection_guard": "Lean kernel rfl plus lean4export exact-constant guard",
        "declarations": declarations,
        "acceptance": "ACCEPTED_V06_FILE",
    }
    args.manifest_output.parent.mkdir(parents=True, exist_ok=True)
    args.manifest_output.write_text(json.dumps(manifest, indent=2) + "\n")
    status = {
        "slice": "TRANSLATION_ORDER_MODEL_PROCESSOR_SUPPLY",
        "per_file": {"model/processor/supply.v": {
            "public_declarations": 5, "translated": 5,
            "proof_clean": 5, "certified": 5,
            "certified_without_prop_sprop_foundation": 2,
            "certified_with_prop_sprop_foundation": 3,
            "status": "ACCEPTED_V06_FILE",
        }},
        "coverage": {
            "accepted_files": 28, "authoritative_files": 357,
            "accepted_declarations": 252,
            "authoritative_declarations": 2439,
            "translated_but_not_certified": 0,
            "deferred_external_boundary": 239,
        },
        "previous_status_sha256": sha(args.previous_status),
        "snapshot_id": args.snapshot_id,
        "status": "PASS",
    }
    args.status_output.write_text(json.dumps(status, indent=2) + "\n")

    begin = "<!-- FORMAL_PUBLICATION_BEGIN -->"
    end = "<!-- FORMAL_PUBLICATION_END -->"
    report = args.canonical_report.read_text()
    if begin in report:
        report = report.split(begin, 1)[0].rstrip() + "\n\n"
    rows = "\n".join(
        f"| `{name}` | `{records[name]['status']}` |" for name in names)
    section = f"""{begin}
## {generated_at} — formal publication accepted

The content-addressed `prepare → check → finalize` run passed for snapshot
`{args.snapshot_id}`. It freshly rebuilt the production dependency closure,
compiled the byte-identical official source file, exported/imported the actual
Lean artifact, regenerated and kernel-checked the artifact adapters, and ran
fail-closed Lean/Rocq assumption audits.

| Declaration | Status |
|---|---|
{rows}

All five results have empty semantic-premise and unexpected-assumption sets,
and false source/target self-dependency flags. The three labelled results use
only the approved `PropSPropFoundation.interpret_strict` boundary. The
Bool-to-Nat operation bridge is independently `CERTIFIED`.

Key hashes: production `.olean` `{manifest['production_olean_sha256']}`,
export `{manifest['export_sha256']}`, imported `.vo`
`{manifest['import_sha256']}`, correspondence `.vo`
`{manifest['correspondence_vo_sha256']}`.

Cumulative machine coverage is **28 / 357 files** and **252 / 2439
declarations**, with zero translated-but-not-certified debt.

Final file status: **ACCEPTED_V06_FILE**.
{end}
"""
    args.canonical_report.write_text(report.rstrip() + "\n\n" + section)
    args.run_report.write_text(args.run_report.read_text() + f"""

## {generated_at} — processor Supply formally accepted

- All five v0.6 definitions passed actual-artifact correspondence and
  fail-closed assumption audits: two `CERTIFIED`, three explicitly
  `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`.
- The new Bool-to-Nat bridge is independently kernel-certified. Semantic
  premises and unexpected assumptions are empty; source/target self-dependency
  flags are false.
- Coverage is now **28 / 357 files** and **252 / 2439 declarations**, with
  zero validation debt.
""")


if __name__ == "__main__":
    main()
