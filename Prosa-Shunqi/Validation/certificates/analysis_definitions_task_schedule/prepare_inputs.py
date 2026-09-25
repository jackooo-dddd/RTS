#!/usr/bin/env python3
"""Prepare Rank 65 certificate inputs for one exact imported artifact.

Only accepted proof sources are replayed.  The Arrival Sequence operation
replay drops its unused JobArrival bridge because this export has no
JobArrival root; no retained definition or proof body is edited.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
from pathlib import Path


PINNED = {
    "Validation/templates/ArtifactBoolListAdapter.v.tpl": "4c9083532755ce19c7e6108b4ab3dfbec2ae44c649b054aa3f32fd258e08000c",
    "Validation/scripts/generate_artifact_bool_list_adapter.py": "e1dcb58acd605d040ae870e0cb85b13b1baded383e03d213e45347cfb7ff5bf6",
    "Validation/scripts/replay_accepted_certificate_sources.py": "ebddfc93af91fb81f9162bf238b4afd6ea8a48c139943ff8cdb02d1a06bf884c",
    "Validation/certificates/common/PropSPropFoundation.v": "ba5c016b0fc2818bab8d9cff63405d58174f6ae5d635f515e76ce8d303327099",
    "Validation/certificates/common/LogicalRelation.v": "08fb13bbc862f346523a056f22687580c5b05f3231d3d94083328deaddcabc04",
    "Validation/certificates/common/SubadditivityNatCorrespondence.v": "99924c979b324df090c2f27fd71d373558ac6a6a3ea0349edf8930276489eba4",
    "Validation/certificates/behavior_arrival_sequence/ArrivalSequenceOperations.v": "b3d8a9f93976846f1777182c55f59b73872f912d8a2534c69e65d1dcbd1778cc",
    "Validation/certificates/behavior_service/ServiceNatBoolOperations.v": "2db3cf9acefae93cc3044bc8fa7e7a44e6b6e0fcb8c15d41cdab7519e8dbb84a",
    "Validation/certificates/behavior_service/ServiceIntervalOperations.v": "21a10cfcecbaa693524609e432c756a15734f8f07ab168bf685de5298cd936e9",
    "Validation/certificates/behavior_service/ServiceScheduleOperations.v": "0d6a3b5b83724244e819e258e5735e8e8ff1a4ab2f0b67cdee6fdff53aac7d4f",
}
SUBADDITIVITY_VO_SHA256 = "9d934dfd1a8c9f5773146cf5f9f97e766e7c39ace3d2a7f371fd1b3890b21452"
ARRIVAL_START = "Definition ArJobArrivalRel (T : eqType)\n"
ARRIVAL_END = "Definition ArArrivalSequenceRel (T : eqType)\n"
ARRIVAL_AUDIT = "Print Assumptions ar_job_arrival_import_certificate.\n"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require_hash(path: Path, expected: str) -> None:
    if not path.is_file() or sha(path) != expected:
        raise SystemExit(f"hash mismatch or missing: {path}; expected {expected}")


def run(*args: str) -> None:
    subprocess.run(args, check=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--accepted-root", required=True, type=Path)
    parser.add_argument("--imported-vo", required=True, type=Path)
    parser.add_argument("--expected-import-sha256", required=True)
    parser.add_argument("--subadditivity-vo", required=True, type=Path)
    parser.add_argument("--imported-dir", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    root = args.accepted_root.resolve()
    for relative, expected in PINNED.items():
        require_hash(root / relative, expected)
    require_hash(args.imported_vo, args.expected_import_sha256)
    require_hash(args.subadditivity_vo, SUBADDITIVITY_VO_SHA256)
    for name in ("behavior_arrival_sequence", "behavior_service"):
        manifest = json.loads(
            (root / f"Validation/planning/v06_pipeline/{name}_module_manifest.json").read_text()
        )
        if manifest.get("acceptance") != "ACCEPTED_V06_FILE":
            raise SystemExit(f"producer not accepted: {name}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    args.imported_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(args.subadditivity_vo, args.imported_dir / "ImportedSubadditivity.vo")
    for name in ("PropSPropFoundation", "LogicalRelation", "SubadditivityNatCorrespondence"):
        shutil.copy2(root / f"Validation/certificates/common/{name}.v", args.output_dir / f"{name}.v")

    generator = root / "Validation/scripts/generate_artifact_bool_list_adapter.py"
    template = root / "Validation/templates/ArtifactBoolListAdapter.v.tpl"
    for prefix, capital, filename, metadata in (
        ("ar", "Ar", "ArrivalSequenceBaseAdapter.v", "arrival_base_adapter.json"),
        ("svc", "Svc", "ServiceBaseAdapter.v", "service_base_adapter.json"),
    ):
        run(
            "python3", str(generator), "--template", str(template),
            "--imported-module", "ImportedTaskSchedule", "--prefix", prefix,
            "--capital-prefix", capital, "--imported-artifact", str(args.imported_vo),
            "--output", str(args.output_dir / filename),
            "--metadata", str(args.output_dir / metadata),
            "--require-operation", "bool.roundtrip", "--require-operation", "bool.truth",
            "--require-operation", "eqtype.decidable_eq",
            "--require-operation", "list.roundtrip", "--require-operation", "list.membership",
        )

    replay = root / "Validation/scripts/replay_accepted_certificate_sources.py"
    run(
        "python3", str(replay),
        "--manifest", str(root / "Validation/planning/v06_pipeline/behavior_arrival_sequence_module_manifest.json"),
        "--source-dir", str(root / "Validation/certificates/behavior_arrival_sequence"),
        "--output-dir", str(args.output_dir),
        "--old-imported", "ImportedArrivalSequence",
        "--new-imported", "ImportedTaskSchedule",
        "ArrivalSequenceOperations.v",
    )
    run(
        "python3", str(replay),
        "--manifest", str(root / "Validation/planning/v06_pipeline/behavior_service_module_manifest.json"),
        "--source-dir", str(root / "Validation/certificates/behavior_service"),
        "--output-dir", str(args.output_dir),
        "--old-imported", "ImportedService",
        "--new-imported", "ImportedTaskSchedule",
        "ServiceNatBoolOperations.v", "ServiceIntervalOperations.v",
        "ServiceScheduleOperations.v",
    )
    arrival = args.output_dir / "ArrivalSequenceOperations.v"
    content = arrival.read_text()
    if content.count(ARRIVAL_START) != 1 or content.count(ARRIVAL_END) != 1:
        raise SystemExit("Arrival Sequence replay boundary changed")
    if content.count(ARRIVAL_AUDIT) != 1:
        raise SystemExit("unused JobArrival audit marker changed")
    start, end = content.index(ARRIVAL_START), content.index(ARRIVAL_END)
    if start >= end:
        raise SystemExit("Arrival Sequence replay order changed")
    arrival.write_text(content[:start] + content[end:].replace(ARRIVAL_AUDIT, ""))
    evidence = {
        "imported_artifact_sha256": sha(args.imported_vo),
        "subadditivity_vo_sha256": sha(args.imported_dir / "ImportedSubadditivity.vo"),
        "operation_slice": "unused JobArrival block removed; all retained proof bytes unchanged",
        "generated": {p.name: sha(p) for p in sorted(args.output_dir.glob("*.v"))},
    }
    (args.output_dir / "task_schedule_prepare_inputs.json").write_text(
        json.dumps(evidence, indent=2, sort_keys=True) + "\n"
    )


if __name__ == "__main__":
    main()
