#!/usr/bin/env bash

# Reuse the already audited Service closure builders, then extend that exact
# dependency snapshot with Ready.  The overrides below are Ready-specific;
# no historical artifact is published by the inherited hooks.
source "$VALIDATION_ROOT/tooling/behavior_service_incremental_hooks.sh"
eval "$(declare -f validation_prepare_lean_build | sed '1s/validation_prepare_lean_build/service_base_prepare_lean_build/')"
eval "$(declare -f validation_prepare_source_acquisition | sed '1s/validation_prepare_source_acquisition/service_base_prepare_source_acquisition/')"

VALIDATION_PREPARE_INPUTS=(
  "$VALIDATION_ROOT/tooling/behavior_ready_incremental_descriptor.json"
  "$VALIDATION_ROOT/tooling/behavior_ready_export_config.json"
  "$VALIDATION_ROOT/tooling/behavior_ready_incremental_hooks.sh"
  "$VALIDATION_ROOT/scripts/run_incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/validation_common.sh"
)

VALIDATION_CHECK_INPUTS=(
  "$VALIDATION_ROOT/scripts/audit_assumptions.py"
  "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py"
  "$VALIDATION_ROOT/scripts/instantiate_service_correspondence.py"
  "$VALIDATION_ROOT/scripts/instantiate_arrival_correspondence.py"
  "$VALIDATION_ROOT/scripts/publish_behavior_ready.py"
  "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl"
  "$VALIDATION_ROOT/certificates/common/PropSPropFoundation.v"
  "$VALIDATION_ROOT/certificates/common/LogicalRelation.v"
  "$VALIDATION_ROOT/certificates/common/SubadditivityNatCorrespondence.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyBaseAdapter.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyNatBoolOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyIntervalOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyScheduleOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyJobOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyServiceCorrespondence.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyArrivalBaseAdapter.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyArrivalOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyArrivalCorrespondence.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyCorrespondence.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyImportedAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadySourceAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyTypeAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ReadyAssumptionAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_ready/ready_assumption_config.json"
  "$VALIDATION_ROOT/certificates/behavior_ready/ready_adapter_assumption_config.json"
)

validation_prepare_lean_build() {
  jq -e '.status == "PASS" and
    .coverage.accepted_files == 25 and
    .coverage.accepted_declarations == 240 and
    .coverage.translated_but_not_certified == 0' \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_service_module_status.json" >/dev/null
  jq -e '.FILE_DAG_READY == true and .public_declarations == 7' \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_ready_selection.json" >/dev/null
  service_base_prepare_lean_build

  if rg -n '\b(sorry|axiom|unsafe)\b' \
      "$PROJECT_ROOT/Prosa/Behavior/Ready.lean" \
      "$VALIDATION_ROOT/fixtures/translation_order/ReadyComputationInterface.lean"; then
    echo "forbidden Lean proof escape in Ready snapshot" >&2
    return 1
  fi
  validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Behavior/Ready" \
    > "$VALIDATION_RUN_LOG/fresh_Ready.log" 2>&1
  mkdir -p "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order"
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/BigcatComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/BigcatComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_bigcat_interface.log" 2>&1
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ReadyComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/ReadyComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_ready_interface.log" 2>&1
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    "$VALIDATION_ROOT/fixtures/translation_order/LeanReadyAudit.lean" \
    > "$VALIDATION_PREPARED/lean_ready_freeze_and_axioms.log" 2>&1
  cp "$VALIDATION_PREPARED/lean_ready_freeze_and_axioms.log" \
    "$VALIDATION_RUN_LOG/lean_ready_freeze_and_axioms.log"
  python3 "$VALIDATION_ROOT/scripts/audit_lean_axioms.py" \
    --config "$VALIDATION_ROOT/fixtures/translation_order/ready_lean_axiom_config.json" \
    --log "$VALIDATION_PREPARED/lean_ready_freeze_and_axioms.log" \
    --output "$VALIDATION_PREPARED/lean_ready_axiom_summary.json" \
    > "$VALIDATION_RUN_LOG/lean_ready_axiom_classifier.log"
  jq -e '(.missing | length) == 0 and (.extra | length) == 0 and
    (.declarations | length) == 19 and
    ([.declarations[] | .status == "PASS" and
      (.unexpected_axioms | length == 0)] | all)' \
    "$VALIDATION_PREPARED/lean_ready_axiom_summary.json" >/dev/null

  python3 - "$VALIDATION_PREPARED/olean" \
    "$VALIDATION_PREPARED/dependency_build_manifest.json" <<'PY'
import hashlib, json, sys
from pathlib import Path
root, output = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
files = sorted(root.rglob("*.olean"))
if len(files) != 30:
    raise SystemExit(f"expected 30 freshly compiled modules, found {len(files)}")
output.write_text(json.dumps({
    "status": "PASS",
    "mode": "FRESH_ACCEPTED_DEPENDENCY_CLOSURE_PLUS_READY_AND_INTERFACES",
    "module_count": len(files),
    "modules": {str(p.relative_to(root)): {
        "sha256": sha(p), "bytes": p.stat().st_size} for p in files},
}, indent=2, sort_keys=True) + "\n")
PY
  VALIDATION_STAGE_OUTPUTS=(
    "util_all_olean=$VALIDATION_PREPARED/olean/Prosa/Util/All.olean"
    "service_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Service.olean"
    "ready_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Ready.olean"
    "schedule_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ScheduleComputationInterface.olean"
    "service_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ServiceComputationInterface.olean"
    "bigcat_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/BigcatComputationInterface.olean"
    "ready_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ReadyComputationInterface.olean"
    "lean_service_axiom_summary=$VALIDATION_PREPARED/lean_axiom_summary.json"
    "lean_ready_axiom_summary=$VALIDATION_PREPARED/lean_ready_axiom_summary.json"
    "dependency_build_manifest=$VALIDATION_PREPARED/dependency_build_manifest.json"
  )
}

validation_prepare_source_acquisition() {
  service_base_prepare_source_acquisition
  cp "$SOURCE_ROOT/behavior/ready.v" \
    "$VALIDATION_PREPARED/source/behavior/ready.v"
  cmp -s "$SOURCE_ROOT/behavior/ready.v" \
    "$VALIDATION_PREPARED/source/behavior/ready.v"
  ulimit -s 65520
  (cd "$VALIDATION_PREPARED/source" && \
    opam exec --switch="$ROCQ_SWITCH" -- rocq c \
      -R "$VALIDATION_PREPARED/source" prosa behavior/ready.v) \
    > "$VALIDATION_RUN_LOG/source_ready.log" 2>&1
  python3 - "$SOURCE_ROOT" "$VALIDATION_ROOT" \
    "$VALIDATION_PREPARED/source" <<'PY'
import csv, hashlib, json, subprocess, sys
from pathlib import Path
source_root, validation, output_root = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
expected = ["JobReady", "backlogged", "jobs_come_from_arrival_sequence",
            "jobs_must_arrive_to_execute", "jobs_must_be_ready_to_execute",
            "completed_jobs_dont_execute", "valid_schedule"]
rows = [r for r in csv.DictReader(
    (validation / "planning/v06_dependency/declaration_inventory.csv").open()
) if r["source_file"] == "behavior/ready.v"]
if [r["declaration_name"] for r in rows] != expected:
    raise SystemExit("authoritative Ready inventory changed")
types = json.loads((validation /
    "planning/v06_dependency/declaration_type_evidence.json").read_text())
declarations = {}
for row in rows:
    evidence = types.get(row["qualified_name"])
    fingerprint = row["final_type_or_type_fingerprint"].removeprefix(
        "rocq-check-sha256:")
    if evidence is None or evidence["sha256"] != fingerprint:
        raise SystemExit(f"elaborated type evidence mismatch: {row['qualified_name']}")
    declarations[row["declaration_name"]] = {
        "qualified_name": row["qualified_name"], "kind": row["kind"],
        "source_command_sha256": row["source_command_sha256"],
        "elaborated_type_sha256": evidence["sha256"],
        "normalized_check": evidence["normalized_check"],
    }
result = {
    "status": "PASS",
    "source_commit": subprocess.check_output(
        ["git", "-C", str(source_root), "rev-parse", "HEAD"], text=True
    ).strip(),
    "source_file": "behavior/ready.v",
    "authoritative_source_sha256": sha(source_root / "behavior/ready.v"),
    "compiled_source_sha256": sha(output_root / "behavior/ready.v"),
    "byte_identical_authoritative_source": True,
    "declarations": declarations,
}
(output_root / "ready_source_acquisition.json").write_text(
    json.dumps(result, indent=2, sort_keys=True) + "\n")
PY
  VALIDATION_STAGE_OUTPUTS=(
    "source_compat=$VALIDATION_PREPARED/source/util/all.vo"
    "source_notation=$VALIDATION_PREPARED/source/util/notation.vo"
    "source_time=$VALIDATION_PREPARED/source/behavior/time.vo"
    "source_job=$VALIDATION_PREPARED/source/behavior/job.vo"
    "source_arrival=$VALIDATION_PREPARED/source/behavior/arrival_sequence.vo"
    "source_schedule=$VALIDATION_PREPARED/source/behavior/schedule.vo"
    "source_service=$VALIDATION_PREPARED/source/behavior/service.vo"
    "source_ready=$VALIDATION_PREPARED/source/behavior/ready.vo"
    "source_metadata=$VALIDATION_PREPARED/source/ready_source_acquisition.json"
  )
}

validation_prepare_export() {
  "$VALIDATION_ROOT/scripts/export_actual_artifact.sh" \
    --config "$VALIDATION_ROOT/tooling/behavior_ready_export_config.json" \
    --output "$VALIDATION_PREPARED/imported/Ready.out" \
    --log "$VALIDATION_RUN_LOG/export.log" \
    --metadata "$VALIDATION_PREPARED/imported/ready_export_metadata.json"
  VALIDATION_STAGE_OUTPUTS=(
    "export=$VALIDATION_PREPARED/imported/Ready.out"
    "export_metadata=$VALIDATION_PREPARED/imported/ready_export_metadata.json"
  )
}

validation_prepare_rocq_import() {
  cp "$VALIDATION_ROOT/imported/foundation_slice_2/Subadditivity.out" \
    "$VALIDATION_PREPARED/imported/Subadditivity.out"
  cp "$VALIDATION_ROOT/imported/foundation_slice_2/ImportedSubadditivity.v" \
    "$VALIDATION_PREPARED/imported/ImportedSubadditivity.v"
  cp "$VALIDATION_ROOT/fixtures/translation_order/ImportedReady.v" \
    "$VALIDATION_PREPARED/imported/ImportedReady.v"
  ulimit -s 65520
  local module
  for module in ImportedSubadditivity ImportedReady; do
    (cd "$VALIDATION_PREPARED/imported" && \
      validation_rocq_compile "$VALIDATION_PREPARED" "${module}.v") \
      > "$VALIDATION_RUN_LOG/import_${module}.log" 2>&1
  done
  VALIDATION_STAGE_OUTPUTS=(
    "subadditivity_export=$VALIDATION_PREPARED/imported/Subadditivity.out"
    "subadditivity_import_vo=$VALIDATION_PREPARED/imported/ImportedSubadditivity.vo"
    "ready_import_source=$VALIDATION_PREPARED/imported/ImportedReady.v"
    "ready_import_vo=$VALIDATION_PREPARED/imported/ImportedReady.vo"
  )
}

validation_check_certificate_compile() {
  local common_dir="$VALIDATION_ROOT/certificates/common"
  local cert_dir="$VALIDATION_ROOT/certificates/behavior_ready"
  mkdir -p "$VALIDATION_PHASE_WORK/certificates"
  cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$cert_dir/"{ReadyCorrespondence,ReadyImportedAudit,ReadySourceAudit,ReadyTypeAudit,ReadyAssumptionAudit}.v \
    "$VALIDATION_PHASE_WORK/certificates/"

  python3 "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py" \
    --template "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl" \
    --imported-module ImportedReady --prefix svc --capital-prefix Svc \
    --imported-artifact "$VALIDATION_PHASE_WORK/imported/ImportedReady.vo" \
    --output "$VALIDATION_PHASE_WORK/certificates/ReadyBaseAdapter.v" \
    --metadata "$VALIDATION_PHASE_WORK/certificates/ready_base_adapter.json" \
    --require-operation bool.roundtrip --require-operation bool.truth \
    --require-operation eqtype.decidable_eq \
    --require-operation list.roundtrip --require-operation list.membership
  cmp -s "$cert_dir/ReadyBaseAdapter.v" \
    "$VALIDATION_PHASE_WORK/certificates/ReadyBaseAdapter.v"
  python3 "$VALIDATION_ROOT/scripts/instantiate_service_correspondence.py" \
    --source-dir "$VALIDATION_ROOT/certificates/behavior_service" \
    --output-dir "$VALIDATION_PHASE_WORK/certificates" \
    --imported-module ImportedReady \
    --imported-artifact "$VALIDATION_PHASE_WORK/imported/ImportedReady.vo" \
    --metadata "$VALIDATION_PHASE_WORK/certificates/ready_service_instantiation.json"
  local module
  for module in ReadyNatBoolOperations ReadyIntervalOperations \
      ReadyScheduleOperations ReadyJobOperations ReadyServiceCorrespondence; do
    cmp -s "$cert_dir/${module}.v" \
      "$VALIDATION_PHASE_WORK/certificates/${module}.v"
  done

  python3 "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py" \
    --template "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl" \
    --imported-module ImportedReady --prefix ar --capital-prefix Ar \
    --imported-artifact "$VALIDATION_PHASE_WORK/imported/ImportedReady.vo" \
    --output "$VALIDATION_PHASE_WORK/certificates/ReadyArrivalBaseAdapter.v" \
    --metadata "$VALIDATION_PHASE_WORK/certificates/ready_arrival_base_adapter.json" \
    --require-operation bool.roundtrip --require-operation bool.truth \
    --require-operation eqtype.decidable_eq \
    --require-operation list.roundtrip --require-operation list.membership
  cmp -s "$cert_dir/ReadyArrivalBaseAdapter.v" \
    "$VALIDATION_PHASE_WORK/certificates/ReadyArrivalBaseAdapter.v"
  python3 "$VALIDATION_ROOT/scripts/instantiate_arrival_correspondence.py" \
    --source-dir "$VALIDATION_ROOT/certificates/behavior_arrival_sequence" \
    --output-dir "$VALIDATION_PHASE_WORK/certificates" \
    --imported-module ImportedReady \
    --imported-artifact "$VALIDATION_PHASE_WORK/imported/ImportedReady.vo" \
    --correspondence-lemma arrival_sequence_correspondence_certificate \
    --correspondence-lemma arrivals_at_correspondence_certificate \
    --correspondence-lemma arrives_at_correspondence_certificate \
    --correspondence-lemma arrives_in_correspondence_certificate \
    --correspondence-lemma has_arrived_correspondence_certificate \
    --metadata "$VALIDATION_PHASE_WORK/certificates/ready_arrival_instantiation.json"
  for module in ReadyArrivalOperations ReadyArrivalCorrespondence; do
    cmp -s "$cert_dir/${module}.v" \
      "$VALIDATION_PHASE_WORK/certificates/${module}.v"
  done

  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' \
      "$VALIDATION_PHASE_WORK/certificates" --glob '*.v' \
      --glob '!PropSPropFoundation.v'; then
    echo "forbidden Ready certificate proof escape" >&2
    return 1
  fi
  ulimit -s 65520
  for module in PropSPropFoundation LogicalRelation \
      SubadditivityNatCorrespondence ReadyBaseAdapter \
      ReadyNatBoolOperations ReadyIntervalOperations ReadyScheduleOperations \
      ReadyJobOperations ReadyServiceCorrespondence ReadyArrivalBaseAdapter \
      ReadyArrivalOperations ReadyArrivalCorrespondence ReadyCorrespondence \
      ReadyImportedAudit ReadySourceAudit ReadyTypeAudit ReadyAssumptionAudit; do
    validation_rocq_compile "$VALIDATION_PHASE_WORK" \
      "$VALIDATION_PHASE_WORK/certificates/${module}.v" \
      > "$VALIDATION_RUN_LOG/rocq_${module}.log" 2>&1
  done
  cp "$VALIDATION_RUN_LOG/rocq_ReadyAssumptionAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  cat "$VALIDATION_RUN_LOG/rocq_ReadyBaseAdapter.log" \
      "$VALIDATION_RUN_LOG/rocq_ReadyArrivalBaseAdapter.log" \
    > "$VALIDATION_PHASE_WORK/certificates/adapter_assumptions.log"
  cp "$VALIDATION_RUN_LOG/rocq_ReadyTypeAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/type_audit.log"
  VALIDATION_STAGE_OUTPUTS=(
    "service_adapter_metadata=$VALIDATION_PHASE_WORK/certificates/ready_base_adapter.json"
    "arrival_adapter_metadata=$VALIDATION_PHASE_WORK/certificates/ready_arrival_base_adapter.json"
    "service_instantiation=$VALIDATION_PHASE_WORK/certificates/ready_service_instantiation.json"
    "arrival_instantiation=$VALIDATION_PHASE_WORK/certificates/ready_arrival_instantiation.json"
    "correspondence_vo=$VALIDATION_PHASE_WORK/certificates/ReadyCorrespondence.vo"
    "type_audit_vo=$VALIDATION_PHASE_WORK/certificates/ReadyTypeAudit.vo"
    "assumption_audit_vo=$VALIDATION_PHASE_WORK/certificates/ReadyAssumptionAudit.vo"
    "type_audit_log=$VALIDATION_PHASE_WORK/certificates/type_audit.log"
    "assumption_log=$VALIDATION_PHASE_WORK/certificates/assumptions.log"
    "adapter_assumption_log=$VALIDATION_PHASE_WORK/certificates/adapter_assumptions.log"
  )
}

validation_check_assumption_audit() {
  local cert_dir="$VALIDATION_ROOT/certificates/behavior_ready"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$cert_dir/ready_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/assumption_classifier.log"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$cert_dir/ready_adapter_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/adapter_assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/adapter_assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/adapter_assumption_classifier.log"
  jq -e '
    (.certificates | length) == 7 and
    ([.certificates[] | select(.status == "CERTIFIED")] | length) == 1 and
    ([.certificates[] | select(.status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")] | length) == 6 and
    ([.certificates[] |
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all)' \
    "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" >/dev/null
  jq -e '
    (.certificates | length) == 12 and
    ([.certificates[] |
      (.status == "CERTIFIED" or
       .status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION") and
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all)' \
    "$VALIDATION_PHASE_WORK/certificates/adapter_assumption_summary.json" >/dev/null
  python3 - \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_service_module_status.json" \
    "$VALIDATION_PHASE_WORK/certificates/baseline_after.json" <<'PY'
import json, sys
from pathlib import Path
source, output = map(Path, sys.argv[1:])
data = json.loads(source.read_text())
ok = (data.get("status") == "PASS"
      and data["coverage"]["accepted_files"] == 25
      and data["coverage"]["accepted_declarations"] == 240
      and data["coverage"]["translated_but_not_certified"] == 0)
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
    "adapter_assumption_summary=$VALIDATION_PHASE_WORK/certificates/adapter_assumption_summary.json"
    "baseline_audit=$VALIDATION_PHASE_WORK/certificates/baseline_after.json"
  )
}

validation_finalize_publication() {
  local publish_dir="$VALIDATION_ROOT/imported/translation_order/ready"
  local pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
  local report="$PROJECT_ROOT/Reports/files/behavior/2026-09-23_042533_ready.md"
  local run_report="$PROJECT_ROOT/Reports/runs/2026-09-22_000308_translation_order_continuous_run.md"
  mkdir -p "$publish_dir" "$(dirname "$report")"
  cp "$VALIDATION_PHASE_WORK/imported/"{Ready.out,ImportedReady.v,ImportedReady.vo} \
    "$publish_dir/"
  local module
  for module in ReadyBaseAdapter ReadyNatBoolOperations \
      ReadyIntervalOperations ReadyScheduleOperations ReadyJobOperations \
      ReadyServiceCorrespondence ReadyArrivalBaseAdapter \
      ReadyArrivalOperations ReadyArrivalCorrespondence ReadyCorrespondence \
      ReadyImportedAudit ReadySourceAudit ReadyTypeAudit ReadyAssumptionAudit; do
    cp "$VALIDATION_PHASE_WORK/certificates/${module}.vo" \
      "$publish_dir/${module}.vo"
  done
  cp "$VALIDATION_PHASE_WORK/certificates/"*.json "$publish_dir/"
  cp "$VALIDATION_PREPARED/lean_ready_axiom_summary.json" \
    "$VALIDATION_PHASE_WORK/lean_ready_axiom_summary.json"
  cp "$VALIDATION_PHASE_WORK/lean_ready_axiom_summary.json" \
    "$publish_dir/lean_ready_axiom_summary.json"
  cp "$VALIDATION_PHASE_WORK/source/ready_source_acquisition.json" \
    "$publish_dir/ready_source_acquisition.json"
  python3 "$VALIDATION_ROOT/scripts/publish_behavior_ready.py" \
    --project "$PROJECT_ROOT" --source "$SOURCE_ROOT" \
    --work "$VALIDATION_PHASE_WORK" --prepared "$VALIDATION_PREPARED" \
    --prepare-evidence "$VALIDATION_PREPARE_EVIDENCE" \
    --snapshot-id "$VALIDATION_SNAPSHOT_ID" \
    --previous-status "$pipeline_dir/behavior_service_module_status.json" \
    --manifest-output "$pipeline_dir/behavior_ready_module_manifest.json" \
    --status-output "$pipeline_dir/behavior_ready_module_status.json" \
    --canonical-report "$report" --run-report "$run_report"
  (cd "$REPO_ROOT" && git diff --check)
  VALIDATION_STAGE_OUTPUTS=(
    "module_manifest=$pipeline_dir/behavior_ready_module_manifest.json"
    "module_status=$pipeline_dir/behavior_ready_module_status.json"
    "canonical_report=$report"
    "published_import=$publish_dir/ImportedReady.vo"
    "published_certificate=$publish_dir/ReadyCorrespondence.vo"
  )
}
