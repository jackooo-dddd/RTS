#!/usr/bin/env bash

VALIDATION_PREPARE_INPUTS=(
  "$VALIDATION_ROOT/tooling/behavior_arrival_sequence_incremental_descriptor.json"
  "$VALIDATION_ROOT/tooling/behavior_arrival_sequence_export_config.json"
  "$VALIDATION_ROOT/tooling/behavior_arrival_sequence_incremental_hooks.sh"
  "$VALIDATION_ROOT/scripts/run_incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/validation_common.sh"
)

VALIDATION_CHECK_INPUTS=(
  "$VALIDATION_ROOT/scripts/audit_assumptions.py"
  "$VALIDATION_ROOT/certificates/common/PropSPropFoundation.v"
  "$VALIDATION_ROOT/certificates/common/LogicalRelation.v"
  "$VALIDATION_ROOT/certificates/common/SubadditivityNatCorrespondence.v"
  "$VALIDATION_ROOT/certificates/behavior_arrival_sequence/ArrivalSequenceBaseAdapter.v"
  "$VALIDATION_ROOT/certificates/behavior_arrival_sequence/ArrivalSequenceOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_arrival_sequence/ArrivalSequenceCorrespondence.v"
  "$VALIDATION_ROOT/certificates/behavior_arrival_sequence/ArrivalSequenceTypeAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_arrival_sequence/ArrivalSequenceAssumptionAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_arrival_sequence/arrival_sequence_assumption_config.json"
)

validation_prepare_lean_build() {
  jq -e '.status == "PASS" and
    .coverage.accepted_files == 22 and
    .coverage.accepted_declarations == 209 and
    .coverage.translated_but_not_certified == 0' \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_job_module_status.json" >/dev/null
  jq -e '.FILE_DAG_READY == true and .public_declarations == 14' \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_arrival_sequence_selection.json" >/dev/null
  if rg -n '\b(sorry|axiom|unsafe)\b' \
      "$PROJECT_ROOT/Prosa/Behavior/Arrival_sequence.lean"; then
    echo "forbidden production proof escape" >&2
    return 1
  fi

  local modules=(
    Tactics Notation Rel Seqset Subadditivity Supremum Nat UnitGrowth
    SearchArg List Sum Epsilon Bigop Setoid Poet Bigcat Minmax Div_mod
    Nondecreasing All
  )
  local module
  for module in "${modules[@]}"; do
    validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Util/$module" \
      > "$VALIDATION_RUN_LOG/fresh_${module}.log" 2>&1
  done
  for module in Time Job Arrival_sequence; do
    validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Behavior/$module" \
      > "$VALIDATION_RUN_LOG/fresh_${module}.log" 2>&1
  done

  mkdir -p \
    "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order"
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/BigcatComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/BigcatComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_bigcat_interface.log" 2>&1
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ArrivalSequenceComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/ArrivalSequenceComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_arrival_interface.log" 2>&1

  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    "$VALIDATION_ROOT/fixtures/translation_order/LeanArrivalSequenceAudit.lean" \
    > "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" 2>&1
  cp "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    "$VALIDATION_RUN_LOG/lean_freeze_and_axioms.log"
  python3 "$VALIDATION_ROOT/scripts/audit_lean_axioms.py" \
    --config "$VALIDATION_ROOT/fixtures/translation_order/arrival_sequence_lean_axiom_config.json" \
    --log "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    --output "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    > "$VALIDATION_RUN_LOG/lean_axiom_classifier.log"
  jq -e '(.missing | length) == 0 and (.extra | length) == 0 and
    (.declarations | length) == 14 and
    ([.declarations[] | .status == "PASS" and
      (.unexpected_axioms | length == 0)] | all)' \
    "$VALIDATION_PREPARED/lean_axiom_summary.json" >/dev/null

  python3 - "$VALIDATION_PREPARED/olean" \
    "$VALIDATION_PREPARED/dependency_build_manifest.json" <<'PY'
import hashlib, json, sys
from pathlib import Path

root, output = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
files = sorted(root.rglob("*.olean"))
expected = 25
if len(files) != expected:
    raise SystemExit(f"expected {expected} freshly compiled modules, found {len(files)}")
result = {
    "status": "PASS",
    "mode": "FRESH_ACCEPTED_DEPENDENCY_CLOSURE_PLUS_TARGET_AND_INTERFACES",
    "module_count": len(files),
    "modules": {
        str(path.relative_to(root)): {
            "sha256": sha(path), "bytes": path.stat().st_size
        }
        for path in files
    },
}
output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
PY
  VALIDATION_STAGE_OUTPUTS=(
    "util_all_olean=$VALIDATION_PREPARED/olean/Prosa/Util/All.olean"
    "time_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Time.olean"
    "job_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Job.olean"
    "arrival_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Arrival_sequence.olean"
    "bigcat_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/BigcatComputationInterface.olean"
    "arrival_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ArrivalSequenceComputationInterface.olean"
    "lean_freeze=$VALIDATION_PREPARED/lean_freeze_and_axioms.log"
    "lean_axiom_summary=$VALIDATION_PREPARED/lean_axiom_summary.json"
    "dependency_build_manifest=$VALIDATION_PREPARED/dependency_build_manifest.json"
  )
}

validation_prepare_source_acquisition() {
  mkdir -p "$VALIDATION_PREPARED/source/util" \
    "$VALIDATION_PREPARED/source/behavior"
  cp "$VALIDATION_ROOT/fixtures/translation_order/source_compat/arrival_sequence/util/all.v" \
    "$VALIDATION_PREPARED/source/util/all.v"
  cp "$SOURCE_ROOT/util/notation.v" \
    "$VALIDATION_PREPARED/source/util/notation.v"
  local source
  for source in time job arrival_sequence; do
    cp "$SOURCE_ROOT/behavior/${source}.v" \
      "$VALIDATION_PREPARED/source/behavior/${source}.v"
  done
  [[ $(validation_sha256 "$VALIDATION_PREPARED/source/behavior/arrival_sequence.v") == \
    5f4aec6937043d7a9f45bdd9ab5cae9097c17eed9fe61f6bc3a906574aa7e9df ]]
  cmp -s "$SOURCE_ROOT/util/notation.v" \
    "$VALIDATION_PREPARED/source/util/notation.v"
  for source in time job arrival_sequence; do
    cmp -s "$SOURCE_ROOT/behavior/${source}.v" \
      "$VALIDATION_PREPARED/source/behavior/${source}.v"
  done
  if rg -n '^(Definition|Class|Record|Structure|Inductive|Variant|Lemma|Theorem|Fact|Remark)\b' \
      "$VALIDATION_PREPARED/source/util/all.v"; then
    echo "Arrival Sequence compatibility interface declares a Prosa symbol" >&2
    return 1
  fi

  ulimit -s 65520
  for source in util/all.v util/notation.v behavior/time.v behavior/job.v \
      behavior/arrival_sequence.v; do
    (cd "$VALIDATION_PREPARED/source" && \
      opam exec --switch="$ROCQ_SWITCH" -- rocq c \
        -R "$VALIDATION_PREPARED/source" prosa "$source") \
      > "$VALIDATION_RUN_LOG/source_$(basename "$source" .v).log" 2>&1
  done

  python3 - "$SOURCE_ROOT" "$VALIDATION_ROOT" \
    "$VALIDATION_PREPARED/source" <<'PY'
import csv, hashlib, json, subprocess, sys
from pathlib import Path

source_root, validation, output_root = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
expected = [
    "arrival_sequence", "arrivals_at", "arrives_at", "arrives_in",
    "consistent_arrival_times", "arrival_sequence_uniq",
    "valid_arrival_sequence", "has_arrived", "arrived_before",
    "arrived_between", "arrivals_between", "arrivals_up_to",
    "arrivals_before", "arrivals_between_P",
]
rows = [r for r in csv.DictReader(
    (validation / "planning/v06_dependency/declaration_inventory.csv").open()
) if r["source_file"] == "behavior/arrival_sequence.v"]
if [r["declaration_name"] for r in rows] != expected:
    raise SystemExit("authoritative Arrival Sequence inventory changed")
types = json.loads(
    (validation / "planning/v06_dependency/declaration_type_evidence.json").read_text()
)
declarations = {}
for row in rows:
    qname = row["qualified_name"]
    evidence = types.get(qname)
    fingerprint = row["final_type_or_type_fingerprint"].removeprefix(
        "rocq-check-sha256:"
    )
    if evidence is None or evidence["sha256"] != fingerprint:
        raise SystemExit(f"elaborated type evidence mismatch: {qname}")
    declarations[row["declaration_name"]] = {
        "qualified_name": qname,
        "kind": row["kind"],
        "source_command_sha256": row["source_command_sha256"],
        "elaborated_type_sha256": evidence["sha256"],
        "normalized_check": evidence["normalized_check"],
    }
result = {
    "status": "PASS",
    "source_commit": subprocess.check_output(
        ["git", "-C", str(source_root), "rev-parse", "HEAD"], text=True
    ).strip(),
    "source_file": "behavior/arrival_sequence.v",
    "authoritative_source_sha256": sha(
        source_root / "behavior/arrival_sequence.v"
    ),
    "compiled_source_sha256": sha(
        output_root / "behavior/arrival_sequence.v"
    ),
    "byte_identical_authoritative_source": True,
    "compatibility_interface": "util/all.v",
    "compatibility_interface_sha256": sha(output_root / "util/all.v"),
    "compatibility_interface_declares_no_prosa_symbol": True,
    "declarations": declarations,
}
(output_root / "arrival_sequence_source_acquisition.json").write_text(
    json.dumps(result, indent=2, sort_keys=True) + "\n"
)
PY
  VALIDATION_STAGE_OUTPUTS=(
    "source_compat=$VALIDATION_PREPARED/source/util/all.vo"
    "source_notation=$VALIDATION_PREPARED/source/util/notation.vo"
    "source_time=$VALIDATION_PREPARED/source/behavior/time.vo"
    "source_job=$VALIDATION_PREPARED/source/behavior/job.vo"
    "source_arrival=$VALIDATION_PREPARED/source/behavior/arrival_sequence.vo"
    "source_metadata=$VALIDATION_PREPARED/source/arrival_sequence_source_acquisition.json"
  )
}

validation_prepare_export() {
  "$VALIDATION_ROOT/scripts/export_actual_artifact.sh" \
    --config "$VALIDATION_ROOT/tooling/behavior_arrival_sequence_export_config.json" \
    --output "$VALIDATION_PREPARED/imported/ArrivalSequence.out" \
    --log "$VALIDATION_RUN_LOG/export.log" \
    --metadata "$VALIDATION_PREPARED/imported/arrival_sequence_export_metadata.json"
  VALIDATION_STAGE_OUTPUTS=(
    "export=$VALIDATION_PREPARED/imported/ArrivalSequence.out"
    "export_metadata=$VALIDATION_PREPARED/imported/arrival_sequence_export_metadata.json"
  )
}

validation_prepare_rocq_import() {
  cp "$VALIDATION_ROOT/imported/foundation_slice_2/Subadditivity.out" \
    "$VALIDATION_PREPARED/imported/Subadditivity.out"
  cp "$VALIDATION_ROOT/imported/foundation_slice_2/ImportedSubadditivity.v" \
    "$VALIDATION_PREPARED/imported/ImportedSubadditivity.v"
  cp "$VALIDATION_ROOT/fixtures/translation_order/ImportedArrivalSequence.v" \
    "$VALIDATION_PREPARED/imported/ImportedArrivalSequence.v"
  ulimit -s 65520
  local module
  for module in ImportedSubadditivity ImportedArrivalSequence; do
    (cd "$VALIDATION_PREPARED/imported" && \
      validation_rocq_compile "$VALIDATION_PREPARED" "${module}.v") \
      > "$VALIDATION_RUN_LOG/import_${module}.log" 2>&1
  done
  VALIDATION_STAGE_OUTPUTS=(
    "subadditivity_export=$VALIDATION_PREPARED/imported/Subadditivity.out"
    "subadditivity_import_source=$VALIDATION_PREPARED/imported/ImportedSubadditivity.v"
    "subadditivity_import_vo=$VALIDATION_PREPARED/imported/ImportedSubadditivity.vo"
    "arrival_import_source=$VALIDATION_PREPARED/imported/ImportedArrivalSequence.v"
    "arrival_import_vo=$VALIDATION_PREPARED/imported/ImportedArrivalSequence.vo"
  )
}

validation_check_setup() {
  cp -R "$VALIDATION_PREPARED/olean/." "$VALIDATION_PHASE_WORK/olean/"
  cp -R "$VALIDATION_PREPARED/source/." "$VALIDATION_PHASE_WORK/source/"
  cp -R "$VALIDATION_PREPARED/imported/." "$VALIDATION_PHASE_WORK/imported/"
  cp "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    "$VALIDATION_PHASE_WORK/lean_freeze_and_axioms.log"
  cp "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    "$VALIDATION_PHASE_WORK/lean_axiom_summary.json"
}

validation_check_certificate_compile() {
  local common_dir="$VALIDATION_ROOT/certificates/common"
  local cert_dir="$VALIDATION_ROOT/certificates/behavior_arrival_sequence"
  mkdir -p "$VALIDATION_PHASE_WORK/certificates"
  cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$cert_dir/"{ArrivalSequenceBaseAdapter,ArrivalSequenceOperations,ArrivalSequenceCorrespondence,ArrivalSequenceTypeAudit,ArrivalSequenceAssumptionAudit}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  local path
  for path in \
      "$cert_dir/ArrivalSequenceBaseAdapter.v" \
      "$cert_dir/ArrivalSequenceOperations.v" \
      "$cert_dir/ArrivalSequenceCorrespondence.v" \
      "$cert_dir/ArrivalSequenceTypeAudit.v" \
      "$cert_dir/ArrivalSequenceAssumptionAudit.v"; do
    if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
      echo "forbidden certificate proof escape in $path" >&2
      return 1
    fi
  done
  ulimit -s 65520
  local module
  for module in PropSPropFoundation LogicalRelation \
      SubadditivityNatCorrespondence ArrivalSequenceBaseAdapter \
      ArrivalSequenceOperations ArrivalSequenceCorrespondence \
      ArrivalSequenceTypeAudit ArrivalSequenceAssumptionAudit; do
    validation_rocq_compile "$VALIDATION_PHASE_WORK" \
      "$VALIDATION_PHASE_WORK/certificates/${module}.v" \
      > "$VALIDATION_RUN_LOG/rocq_${module}.log" 2>&1
  done
  cp "$VALIDATION_RUN_LOG/rocq_ArrivalSequenceAssumptionAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  cp "$VALIDATION_RUN_LOG/rocq_ArrivalSequenceTypeAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/type_audit.log"
  VALIDATION_STAGE_OUTPUTS=(
    "base_adapter_vo=$VALIDATION_PHASE_WORK/certificates/ArrivalSequenceBaseAdapter.vo"
    "operations_vo=$VALIDATION_PHASE_WORK/certificates/ArrivalSequenceOperations.vo"
    "certificate_vo=$VALIDATION_PHASE_WORK/certificates/ArrivalSequenceCorrespondence.vo"
    "type_audit_vo=$VALIDATION_PHASE_WORK/certificates/ArrivalSequenceTypeAudit.vo"
    "assumption_audit_vo=$VALIDATION_PHASE_WORK/certificates/ArrivalSequenceAssumptionAudit.vo"
    "type_audit_log=$VALIDATION_PHASE_WORK/certificates/type_audit.log"
    "assumption_log=$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  )
}

validation_check_assumption_audit() {
  local cert_dir="$VALIDATION_ROOT/certificates/behavior_arrival_sequence"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$cert_dir/arrival_sequence_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/assumption_classifier.log"
  jq -e '
    (.certificates | length) == 14 and
    ([.certificates[] | select(.status == "CERTIFIED")] | length) == 2 and
    ([.certificates[] |
      select(.status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")] | length) == 12 and
    ([.certificates[] |
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all)' \
    "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" >/dev/null
  python3 - \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_job_module_status.json" \
    "$VALIDATION_PHASE_WORK/certificates/baseline_after.json" <<'PY'
import json, sys
from pathlib import Path

source, output = map(Path, sys.argv[1:])
data = json.loads(source.read_text())
ok = (
    data.get("status") == "PASS"
    and data["coverage"]["accepted_files"] == 22
    and data["coverage"]["accepted_declarations"] == 209
    and data["coverage"]["translated_but_not_certified"] == 0
)
output.write_text(json.dumps({
    "status": "PASS" if ok else "FAIL_BASELINE",
    "accepted_files": data["coverage"]["accepted_files"],
    "accepted_declarations": data["coverage"]["accepted_declarations"],
}, indent=2) + "\n")
if not ok:
    raise SystemExit(1)
PY
  [[ -z $(git -C "$REPO_ROOT" status --short -- Prosa-fei) ]]
  VALIDATION_STAGE_OUTPUTS=(
    "assumption_summary=$VALIDATION_PHASE_WORK/certificates/assumption_summary.json"
    "baseline_audit=$VALIDATION_PHASE_WORK/certificates/baseline_after.json"
  )
}

validation_finalize_publication() {
  local cert_dir="$VALIDATION_ROOT/certificates/behavior_arrival_sequence"
  local publish_dir="$VALIDATION_ROOT/imported/translation_order/arrival_sequence"
  local pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
  local report="$PROJECT_ROOT/Reports/files/behavior/2026-09-22_222929_arrival_sequence.md"
  mkdir -p "$publish_dir" "$(dirname "$report")"
  cp "$VALIDATION_PHASE_WORK/imported/"{ArrivalSequence.out,ImportedArrivalSequence.v,ImportedArrivalSequence.vo} \
    "$publish_dir/"
  local module
  for module in ArrivalSequenceBaseAdapter ArrivalSequenceOperations \
      ArrivalSequenceCorrespondence ArrivalSequenceTypeAudit \
      ArrivalSequenceAssumptionAudit; do
    cp "$VALIDATION_PHASE_WORK/certificates/${module}.vo" \
      "$publish_dir/${module}.vo"
  done
  cp "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    "$publish_dir/assumption_summary.json"
  cp "$VALIDATION_PHASE_WORK/lean_axiom_summary.json" \
    "$publish_dir/lean_axiom_summary.json"
  cp "$VALIDATION_PHASE_WORK/source/arrival_sequence_source_acquisition.json" \
    "$publish_dir/arrival_sequence_source_acquisition.json"

  python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$VALIDATION_PHASE_WORK" \
    "$VALIDATION_PREPARED" "$VALIDATION_PREPARE_EVIDENCE" \
    "$VALIDATION_SNAPSHOT_ID" \
    "$pipeline_dir/behavior_job_module_status.json" \
    "$pipeline_dir/behavior_arrival_sequence_module_manifest.json" \
    "$pipeline_dir/behavior_arrival_sequence_module_status.json" \
    "$report" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

(project, source, work, prepared, prepare_evidence, snapshot_id,
 previous_path, manifest_out, status_out, report_out) = sys.argv[1:]
project, source, work, prepared, prepare_evidence = map(
    Path, (project, source, work, prepared, prepare_evidence)
)
previous_path, manifest_out, status_out, report_out = map(
    Path, (previous_path, manifest_out, status_out, report_out)
)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
previous = json.loads(previous_path.read_text())
assumptions = json.loads(
    (work / "certificates/assumption_summary.json").read_text()
)
source_meta = json.loads(
    (work / "source/arrival_sequence_source_acquisition.json").read_text()
)
prepare_run = json.loads(prepare_evidence.read_text())
names = [
    "arrival_sequence", "arrivals_at", "arrives_at", "arrives_in",
    "consistent_arrival_times", "arrival_sequence_uniq",
    "valid_arrival_sequence", "has_arrived", "arrived_before",
    "arrived_between", "arrivals_between", "arrivals_up_to",
    "arrivals_before", "arrivals_between_P",
]
assert previous["coverage"]["accepted_files"] == 22
assert previous["coverage"]["accepted_declarations"] == 209
assert len(assumptions["certificates"]) == 14
assert list(assumptions["certificates"]) == names
assert sum(
    x["status"] == "CERTIFIED"
    for x in assumptions["certificates"].values()
) == 2
assert sum(
    x["status"] == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"
    for x in assumptions["certificates"].values()
) == 12

declarations = []
for name in names:
    record = assumptions["certificates"][name]
    declarations.append({
        "source_declaration": f"prosa.behavior.arrival_sequence.{name}",
        "lean_declaration": f"Prosa.Behavior.Arrival_sequence.{name}",
        "kind": source_meta["declarations"][name]["kind"],
        "source_command_sha256": source_meta["declarations"][name]["source_command_sha256"],
        "source_elaborated_type_sha256": source_meta["declarations"][name]["elaborated_type_sha256"],
        "semantic_status": record["status"],
        "certificate": record["certificate"],
        "semantic_premises": record["semantic_premises"],
        "prop_sprop_foundation": record["prop_sprop_foundation"],
        "unexpected_assumptions": record["unexpected"],
        "source_theorem_dependency": record["source_theorem_dependency"],
        "target_theorem_dependency": record["target_theorem_dependency"],
        "acceptance": "ACCEPTED_V06_TRANSLATION",
    })

manifest = {
    "slice": "TRANSLATION_ORDER_BEHAVIOR_ARRIVAL_SEQUENCE",
    "generated_at": datetime.now().astimezone().isoformat(),
    "source_file": "behavior/arrival_sequence.v",
    "source_commit": subprocess.check_output(
        ["git", "-C", str(source), "rev-parse", "HEAD"], text=True
    ).strip(),
    "source_file_sha256": sha(source / "behavior/arrival_sequence.v"),
    "source_acquisition_sha256": sha(
        work / "source/arrival_sequence_source_acquisition.json"
    ),
    "production_file": "Prosa/Behavior/Arrival_sequence.lean",
    "production_source_sha256": sha(
        project / "Prosa/Behavior/Arrival_sequence.lean"
    ),
    "production_olean_sha256": sha(
        work / "olean/Prosa/Behavior/Arrival_sequence.olean"
    ),
    "computation_interface_olean_sha256": sha(
        work / "olean/Validation/fixtures/translation_order/ArrivalSequenceComputationInterface.olean"
    ),
    "export_sha256": sha(work / "imported/ArrivalSequence.out"),
    "import_sha256": sha(work / "imported/ImportedArrivalSequence.vo"),
    "base_adapter_source_sha256": sha(
        project / "Validation/certificates/behavior_arrival_sequence/ArrivalSequenceBaseAdapter.v"
    ),
    "base_adapter_vo_sha256": sha(
        work / "certificates/ArrivalSequenceBaseAdapter.vo"
    ),
    "operations_source_sha256": sha(
        project / "Validation/certificates/behavior_arrival_sequence/ArrivalSequenceOperations.v"
    ),
    "operations_vo_sha256": sha(
        work / "certificates/ArrivalSequenceOperations.vo"
    ),
    "certificate_source_sha256": sha(
        project / "Validation/certificates/behavior_arrival_sequence/ArrivalSequenceCorrespondence.v"
    ),
    "certificate_vo_sha256": sha(
        work / "certificates/ArrivalSequenceCorrespondence.vo"
    ),
    "type_audit_vo_sha256": sha(
        work / "certificates/ArrivalSequenceTypeAudit.vo"
    ),
    "assumption_audit_vo_sha256": sha(
        work / "certificates/ArrivalSequenceAssumptionAudit.vo"
    ),
    "lean_axiom_summary_sha256": sha(work / "lean_axiom_summary.json"),
    "assumption_summary_sha256": sha(
        work / "certificates/assumption_summary.json"
    ),
    "snapshot_id": snapshot_id,
    "prepare_mode": prepare_run["run_mode"],
    "prepare_evidence_sha256": sha(prepare_evidence),
    "declarations": declarations,
    "acceptance": "ACCEPTED_V06_FILE",
}
manifest_out.write_text(
    json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"
)
status = {
    "slice": "TRANSLATION_ORDER_BEHAVIOR_ARRIVAL_SEQUENCE",
    "per_file": {
        "behavior/arrival_sequence.v": {
            "public_declarations": 14,
            "translated": 14,
            "proof_clean": 14,
            "certified": 14,
            "certified_without_prop_sprop_foundation": 2,
            "certified_with_prop_sprop_foundation": 12,
            "status": "ACCEPTED_V06_FILE",
        }
    },
    "coverage": {
        "accepted_files": 23,
        "authoritative_files": 357,
        "accepted_declarations": 223,
        "authoritative_declarations": 2439,
        "translated_but_not_certified": 0,
        "deferred_external_boundary": 239,
    },
    "previous_status_sha256": sha(previous_path),
    "snapshot_id": snapshot_id,
    "status": "PASS",
}
status_out.write_text(json.dumps(status, indent=2) + "\n")

text = report_out.read_text() if report_out.exists() else ""
begin = "<!-- FORMAL_PUBLICATION_BEGIN -->"
end = "<!-- FORMAL_PUBLICATION_END -->"
if begin in text:
    text = text.split(begin, 1)[0].rstrip() + "\n\n"
section = f"""{begin}
## {manifest['generated_at']} — formal clean publication accepted

The workspace-local incremental validator completed a `CLEAN_FULL`
prepare/check/finalize run for the frozen production snapshot
`{snapshot_id}`. It freshly compiled 25 Lean modules (the accepted utility
closure, Time, Job, Arrival Sequence, and two actual-artifact computation
interfaces), compiled the exact byte-identical official source chain, exported
the computation interface, imported it into Rocq, rebuilt every certificate,
and ran fail-closed Lean/Rocq assumption audits.

Final classification:

| Class | Count |
|---|---:|
| `CERTIFIED` | 2 |
| `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` | 12 |
| semantic premises | 0 |
| source/target self-dependencies | 0 |
| unexpected assumptions | 0 |

The accepted file adds all 14 authoritative declarations. Cumulative machine
coverage is **23 / 357 files** and **223 / 2439 declarations**, with zero
translated-but-not-certified debt. `Prosa-fei/` remained unchanged.

Key formal artifact hashes are the production `.olean`
`{manifest['production_olean_sha256']}`, export `{manifest['export_sha256']}`,
import `{manifest['import_sha256']}`, and correspondence certificate
`{manifest['certificate_vo_sha256']}`.

Final file status: **ACCEPTED_V06_FILE**.
{end}
"""
report_out.write_text(text.rstrip() + "\n\n" + section)
PY
  (cd "$REPO_ROOT" && git diff --check)
  VALIDATION_STAGE_OUTPUTS=(
    "module_manifest=$pipeline_dir/behavior_arrival_sequence_module_manifest.json"
    "module_status=$pipeline_dir/behavior_arrival_sequence_module_status.json"
    "canonical_report=$report"
    "published_import=$publish_dir/ImportedArrivalSequence.vo"
    "published_certificate=$publish_dir/ArrivalSequenceCorrespondence.vo"
  )
}
