#!/usr/bin/env bash

VALIDATION_PREPARE_INPUTS=(
  "$VALIDATION_ROOT/tooling/behavior_service_incremental_descriptor.json"
  "$VALIDATION_ROOT/tooling/behavior_service_export_config.json"
  "$VALIDATION_ROOT/tooling/behavior_service_incremental_hooks.sh"
  "$VALIDATION_ROOT/scripts/run_incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/validation_common.sh"
)

VALIDATION_CHECK_INPUTS=(
  "$VALIDATION_ROOT/scripts/audit_assumptions.py"
  "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py"
  "$VALIDATION_ROOT/scripts/publish_behavior_service.py"
  "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl"
  "$VALIDATION_ROOT/certificates/common/PropSPropFoundation.v"
  "$VALIDATION_ROOT/certificates/common/LogicalRelation.v"
  "$VALIDATION_ROOT/certificates/common/SubadditivityNatCorrespondence.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceBaseAdapter.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceNatBoolOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceIntervalOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceScheduleOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceJobOperations.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceCorrespondence.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceImportedAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceSourceAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceTypeAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_service/ServiceAssumptionAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_service/service_assumption_config.json"
  "$VALIDATION_ROOT/certificates/behavior_service/service_adapter_assumption_config.json"
)

validation_prepare_lean_build() {
  jq -e '.status == "PASS" and
    .coverage.accepted_files == 24 and
    .coverage.accepted_declarations == 228 and
    .coverage.translated_but_not_certified == 0' \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_schedule_module_status.json" >/dev/null
  jq -e '.FILE_DAG_READY == true and .public_declarations == 12' \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_service_selection.json" >/dev/null
  if rg -n '\b(sorry|axiom|unsafe)\b' \
      "$PROJECT_ROOT/Prosa/Behavior/Service.lean" \
      "$VALIDATION_ROOT/fixtures/translation_order/ServiceComputationInterface.lean"; then
    echo "forbidden Lean proof escape in Service snapshot" >&2
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
  for module in Time Job Arrival_sequence Schedule Service; do
    validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Behavior/$module" \
      > "$VALIDATION_RUN_LOG/fresh_${module}.log" 2>&1
  done

  mkdir -p "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order"
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ScheduleComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/ScheduleComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_schedule_interface.log" 2>&1
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ServiceComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/ServiceComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_service_interface.log" 2>&1

  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    "$VALIDATION_ROOT/fixtures/translation_order/LeanServiceAudit.lean" \
    > "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" 2>&1
  cp "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    "$VALIDATION_RUN_LOG/lean_freeze_and_axioms.log"
  python3 "$VALIDATION_ROOT/scripts/audit_lean_axioms.py" \
    --config "$VALIDATION_ROOT/fixtures/translation_order/service_lean_axiom_config.json" \
    --log "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    --output "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    > "$VALIDATION_RUN_LOG/lean_axiom_classifier.log"
  jq -e '(.missing | length) == 0 and (.extra | length) == 0 and
    (.declarations | length) == 50 and
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
expected = 27
if len(files) != expected:
    raise SystemExit(f"expected {expected} freshly compiled modules, found {len(files)}")
output.write_text(json.dumps({
    "status": "PASS",
    "mode": "FRESH_ACCEPTED_DEPENDENCY_CLOSURE_PLUS_SERVICE_AND_INTERFACES",
    "module_count": len(files),
    "modules": {str(p.relative_to(root)): {
        "sha256": sha(p), "bytes": p.stat().st_size} for p in files},
}, indent=2, sort_keys=True) + "\n")
PY
  VALIDATION_STAGE_OUTPUTS=(
    "util_all_olean=$VALIDATION_PREPARED/olean/Prosa/Util/All.olean"
    "schedule_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Schedule.olean"
    "service_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Service.olean"
    "schedule_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ScheduleComputationInterface.olean"
    "service_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ServiceComputationInterface.olean"
    "lean_freeze=$VALIDATION_PREPARED/lean_freeze_and_axioms.log"
    "lean_axiom_summary=$VALIDATION_PREPARED/lean_axiom_summary.json"
    "dependency_build_manifest=$VALIDATION_PREPARED/dependency_build_manifest.json"
  )
}

validation_prepare_source_acquisition() {
  mkdir -p "$VALIDATION_PREPARED/source/util" "$VALIDATION_PREPARED/source/behavior"
  cp "$VALIDATION_ROOT/fixtures/translation_order/source_compat/arrival_sequence/util/all.v" \
    "$VALIDATION_PREPARED/source/util/all.v"
  cp "$SOURCE_ROOT/util/notation.v" "$VALIDATION_PREPARED/source/util/notation.v"
  local source
  for source in time job arrival_sequence schedule service; do
    cp "$SOURCE_ROOT/behavior/${source}.v" \
      "$VALIDATION_PREPARED/source/behavior/${source}.v"
    cmp -s "$SOURCE_ROOT/behavior/${source}.v" \
      "$VALIDATION_PREPARED/source/behavior/${source}.v"
  done
  [[ $(validation_sha256 "$VALIDATION_PREPARED/source/behavior/service.v") == \
    3fd8cf88d667d3c43fae1a7ec62a88f6cef75fcd8e622a59f5a747153c1c4870 ]]
  if rg -n '^(Definition|Class|Record|Structure|Inductive|Variant|Lemma|Theorem|Fact|Remark)\b' \
      "$VALIDATION_PREPARED/source/util/all.v"; then
    echo "Service compatibility interface declares a Prosa symbol" >&2
    return 1
  fi

  ulimit -s 65520
  for source in util/all.v util/notation.v behavior/time.v behavior/job.v \
      behavior/arrival_sequence.v behavior/schedule.v behavior/service.v; do
    (cd "$VALIDATION_PREPARED/source" && \
      opam exec --switch="$ROCQ_SWITCH" -- rocq c \
        -R "$VALIDATION_PREPARED/source" prosa "$source") \
      > "$VALIDATION_RUN_LOG/source_$(basename "$source" .v).log" 2>&1
  done

  python3 - "$SOURCE_ROOT" "$VALIDATION_ROOT" "$VALIDATION_PREPARED/source" <<'PY'
import csv, hashlib, json, subprocess, sys
from pathlib import Path
source_root, validation, output_root = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
expected = ["scheduled_at", "service_at", "receives_service_at",
            "service_during", "service", "completed_by", "completes_at",
            "job_response_time_bound", "job_meets_deadline", "pending",
            "pending_earlier_and_at", "remaining_cost"]
rows = [r for r in csv.DictReader(
    (validation / "planning/v06_dependency/declaration_inventory.csv").open()
) if r["source_file"] == "behavior/service.v"]
if [r["declaration_name"] for r in rows] != expected:
    raise SystemExit("authoritative Service inventory changed")
types = json.loads((validation /
    "planning/v06_dependency/declaration_type_evidence.json").read_text())
declarations = {}
for row in rows:
    qname = row["qualified_name"]
    evidence = types.get(qname)
    fingerprint = row["final_type_or_type_fingerprint"].removeprefix(
        "rocq-check-sha256:")
    if evidence is None or evidence["sha256"] != fingerprint:
        raise SystemExit(f"elaborated type evidence mismatch: {qname}")
    declarations[row["declaration_name"]] = {
        "qualified_name": qname, "kind": row["kind"],
        "source_command_sha256": row["source_command_sha256"],
        "elaborated_type_sha256": evidence["sha256"],
        "normalized_check": evidence["normalized_check"],
    }
result = {
    "status": "PASS",
    "source_commit": subprocess.check_output(
        ["git", "-C", str(source_root), "rev-parse", "HEAD"], text=True
    ).strip(),
    "source_file": "behavior/service.v",
    "authoritative_source_sha256": sha(source_root / "behavior/service.v"),
    "compiled_source_sha256": sha(output_root / "behavior/service.v"),
    "byte_identical_authoritative_source": True,
    "compatibility_interface": "util/all.v",
    "compatibility_interface_sha256": sha(output_root / "util/all.v"),
    "compatibility_interface_declares_no_prosa_symbol": True,
    "declarations": declarations,
}
(output_root / "service_source_acquisition.json").write_text(
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
    "source_metadata=$VALIDATION_PREPARED/source/service_source_acquisition.json"
  )
}

validation_prepare_export() {
  "$VALIDATION_ROOT/scripts/export_actual_artifact.sh" \
    --config "$VALIDATION_ROOT/tooling/behavior_service_export_config.json" \
    --output "$VALIDATION_PREPARED/imported/Service.out" \
    --log "$VALIDATION_RUN_LOG/export.log" \
    --metadata "$VALIDATION_PREPARED/imported/service_export_metadata.json"
  VALIDATION_STAGE_OUTPUTS=(
    "export=$VALIDATION_PREPARED/imported/Service.out"
    "export_metadata=$VALIDATION_PREPARED/imported/service_export_metadata.json"
  )
}

validation_prepare_rocq_import() {
  cp "$VALIDATION_ROOT/imported/foundation_slice_2/Subadditivity.out" \
    "$VALIDATION_PREPARED/imported/Subadditivity.out"
  cp "$VALIDATION_ROOT/imported/foundation_slice_2/ImportedSubadditivity.v" \
    "$VALIDATION_PREPARED/imported/ImportedSubadditivity.v"
  cp "$VALIDATION_ROOT/fixtures/translation_order/ImportedService.v" \
    "$VALIDATION_PREPARED/imported/ImportedService.v"
  ulimit -s 65520
  local module
  for module in ImportedSubadditivity ImportedService; do
    (cd "$VALIDATION_PREPARED/imported" && \
      validation_rocq_compile "$VALIDATION_PREPARED" "${module}.v") \
      > "$VALIDATION_RUN_LOG/import_${module}.log" 2>&1
  done
  VALIDATION_STAGE_OUTPUTS=(
    "subadditivity_export=$VALIDATION_PREPARED/imported/Subadditivity.out"
    "subadditivity_import_source=$VALIDATION_PREPARED/imported/ImportedSubadditivity.v"
    "subadditivity_import_vo=$VALIDATION_PREPARED/imported/ImportedSubadditivity.vo"
    "service_import_source=$VALIDATION_PREPARED/imported/ImportedService.v"
    "service_import_vo=$VALIDATION_PREPARED/imported/ImportedService.vo"
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
  local cert_dir="$VALIDATION_ROOT/certificates/behavior_service"
  mkdir -p "$VALIDATION_PHASE_WORK/certificates"
  cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$cert_dir/"{ServiceNatBoolOperations,ServiceIntervalOperations,ServiceScheduleOperations,ServiceJobOperations,ServiceCorrespondence,ServiceImportedAudit,ServiceSourceAudit,ServiceTypeAudit,ServiceAssumptionAudit}.v \
    "$VALIDATION_PHASE_WORK/certificates/"

  python3 "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py" \
    --template "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl" \
    --imported-module ImportedService --prefix svc --capital-prefix Svc \
    --imported-artifact "$VALIDATION_PHASE_WORK/imported/ImportedService.vo" \
    --output "$VALIDATION_PHASE_WORK/certificates/ServiceBaseAdapter.v" \
    --metadata "$VALIDATION_PHASE_WORK/certificates/service_base_adapter.json" \
    --require-operation bool.roundtrip --require-operation bool.truth \
    --require-operation eqtype.decidable_eq \
    --require-operation list.roundtrip --require-operation list.membership
  cmp -s "$cert_dir/ServiceBaseAdapter.v" \
    "$VALIDATION_PHASE_WORK/certificates/ServiceBaseAdapter.v"

  local path
  for path in "$cert_dir"/*.v; do
    if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
      echo "forbidden certificate proof escape in $path" >&2
      return 1
    fi
  done

  ulimit -s 65520
  local module
  for module in PropSPropFoundation LogicalRelation \
      SubadditivityNatCorrespondence ServiceBaseAdapter \
      ServiceNatBoolOperations ServiceIntervalOperations \
      ServiceScheduleOperations ServiceJobOperations ServiceCorrespondence \
      ServiceImportedAudit ServiceSourceAudit ServiceTypeAudit \
      ServiceAssumptionAudit; do
    validation_rocq_compile "$VALIDATION_PHASE_WORK" \
      "$VALIDATION_PHASE_WORK/certificates/${module}.v" \
      > "$VALIDATION_RUN_LOG/rocq_${module}.log" 2>&1
  done
  cp "$VALIDATION_RUN_LOG/rocq_ServiceAssumptionAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  cp "$VALIDATION_RUN_LOG/rocq_ServiceBaseAdapter.log" \
    "$VALIDATION_PHASE_WORK/certificates/adapter_assumptions.log"
  cp "$VALIDATION_RUN_LOG/rocq_ServiceTypeAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/type_audit.log"
  VALIDATION_STAGE_OUTPUTS=(
    "adapter_metadata=$VALIDATION_PHASE_WORK/certificates/service_base_adapter.json"
    "adapter_vo=$VALIDATION_PHASE_WORK/certificates/ServiceBaseAdapter.vo"
    "nat_bool_operations_vo=$VALIDATION_PHASE_WORK/certificates/ServiceNatBoolOperations.vo"
    "interval_operations_vo=$VALIDATION_PHASE_WORK/certificates/ServiceIntervalOperations.vo"
    "schedule_operations_vo=$VALIDATION_PHASE_WORK/certificates/ServiceScheduleOperations.vo"
    "job_operations_vo=$VALIDATION_PHASE_WORK/certificates/ServiceJobOperations.vo"
    "correspondence_vo=$VALIDATION_PHASE_WORK/certificates/ServiceCorrespondence.vo"
    "type_audit_vo=$VALIDATION_PHASE_WORK/certificates/ServiceTypeAudit.vo"
    "assumption_audit_vo=$VALIDATION_PHASE_WORK/certificates/ServiceAssumptionAudit.vo"
    "type_audit_log=$VALIDATION_PHASE_WORK/certificates/type_audit.log"
    "assumption_log=$VALIDATION_PHASE_WORK/certificates/assumptions.log"
    "adapter_assumption_log=$VALIDATION_PHASE_WORK/certificates/adapter_assumptions.log"
  )
}

validation_check_assumption_audit() {
  local cert_dir="$VALIDATION_ROOT/certificates/behavior_service"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$cert_dir/service_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/assumption_classifier.log"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$cert_dir/service_adapter_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/adapter_assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/adapter_assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/adapter_assumption_classifier.log"
  jq -e '
    (.certificates | length) == 12 and
    ([.certificates[] | select(.status == "CERTIFIED")] | length) == 5 and
    ([.certificates[] | select(.status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")] | length) == 7 and
    ([.certificates[] |
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all)' \
    "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" >/dev/null
  jq -e '
    (.certificates | length) == 6 and
    ([.certificates[] |
      (.status == "CERTIFIED" or
       .status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION") and
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all)' \
    "$VALIDATION_PHASE_WORK/certificates/adapter_assumption_summary.json" >/dev/null
  python3 - \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_schedule_module_status.json" \
    "$VALIDATION_PHASE_WORK/certificates/baseline_after.json" <<'PY'
import json, sys
from pathlib import Path
source, output = map(Path, sys.argv[1:])
data = json.loads(source.read_text())
ok = (data.get("status") == "PASS"
      and data["coverage"]["accepted_files"] == 24
      and data["coverage"]["accepted_declarations"] == 228
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
  local publish_dir="$VALIDATION_ROOT/imported/translation_order/service"
  local pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
  local report="$PROJECT_ROOT/Reports/files/behavior/2026-09-23_023952_service.md"
  local run_report="$PROJECT_ROOT/Reports/runs/2026-09-22_000308_translation_order_continuous_run.md"
  mkdir -p "$publish_dir" "$(dirname "$report")"
  cp "$VALIDATION_PHASE_WORK/imported/"{Service.out,ImportedService.v,ImportedService.vo} \
    "$publish_dir/"
  local module
  for module in ServiceBaseAdapter ServiceNatBoolOperations \
      ServiceIntervalOperations ServiceScheduleOperations ServiceJobOperations \
      ServiceCorrespondence ServiceImportedAudit ServiceSourceAudit \
      ServiceTypeAudit ServiceAssumptionAudit; do
    cp "$VALIDATION_PHASE_WORK/certificates/${module}.vo" \
      "$publish_dir/${module}.vo"
  done
  cp "$VALIDATION_PHASE_WORK/certificates/service_base_adapter.json" \
    "$publish_dir/service_base_adapter.json"
  cp "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    "$publish_dir/assumption_summary.json"
  cp "$VALIDATION_PHASE_WORK/certificates/adapter_assumption_summary.json" \
    "$publish_dir/adapter_assumption_summary.json"
  cp "$VALIDATION_PHASE_WORK/lean_axiom_summary.json" \
    "$publish_dir/lean_axiom_summary.json"
  cp "$VALIDATION_PHASE_WORK/source/service_source_acquisition.json" \
    "$publish_dir/service_source_acquisition.json"

  python3 "$VALIDATION_ROOT/scripts/publish_behavior_service.py" \
    --project "$PROJECT_ROOT" --source "$SOURCE_ROOT" \
    --work "$VALIDATION_PHASE_WORK" --prepared "$VALIDATION_PREPARED" \
    --prepare-evidence "$VALIDATION_PREPARE_EVIDENCE" \
    --snapshot-id "$VALIDATION_SNAPSHOT_ID" \
    --previous-status "$pipeline_dir/behavior_schedule_module_status.json" \
    --manifest-output "$pipeline_dir/behavior_service_module_manifest.json" \
    --status-output "$pipeline_dir/behavior_service_module_status.json" \
    --canonical-report "$report" --run-report "$run_report"
  (cd "$REPO_ROOT" && git diff --check)
  VALIDATION_STAGE_OUTPUTS=(
    "module_manifest=$pipeline_dir/behavior_service_module_manifest.json"
    "module_status=$pipeline_dir/behavior_service_module_status.json"
    "canonical_report=$report"
    "published_import=$publish_dir/ImportedService.vo"
    "published_certificate=$publish_dir/ServiceCorrespondence.vo"
  )
}
