#!/usr/bin/env bash

VALIDATION_PREPARE_INPUTS=(
  "$VALIDATION_ROOT/tooling/model_processor_supply_incremental_descriptor.json"
  "$VALIDATION_ROOT/tooling/model_processor_supply_export_config.json"
  "$VALIDATION_ROOT/tooling/model_processor_supply_incremental_hooks.sh"
  "$VALIDATION_ROOT/scripts/run_incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/validation_common.sh"
)

VALIDATION_CHECK_INPUTS=(
  "$VALIDATION_ROOT/scripts/audit_assumptions.py"
  "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py"
  "$VALIDATION_ROOT/scripts/instantiate_schedule_correspondence.py"
  "$VALIDATION_ROOT/scripts/instantiate_service_correspondence.py"
  "$VALIDATION_ROOT/scripts/publish_model_processor_supply.py"
  "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl"
  "$VALIDATION_ROOT/certificates/common/PropSPropFoundation.v"
  "$VALIDATION_ROOT/certificates/common/LogicalRelation.v"
  "$VALIDATION_ROOT/certificates/common/SubadditivityNatCorrespondence.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyScheduleBaseAdapter.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyScheduleFiniteOperations.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyScheduleOperations.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyBaseAdapter.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyNatBoolOperations.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyIntervalOperations.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyCorrespondence.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyImportedAudit.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplySourceAudit.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyTypeAudit.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/SupplyAssumptionAudit.v"
  "$VALIDATION_ROOT/certificates/model_processor_supply/supply_assumption_config.json"
  "$VALIDATION_ROOT/certificates/model_processor_supply/supply_adapter_assumption_config.json"
)

validation_prepare_lean_build() {
  jq -e '.status == "PASS" and
    .coverage.accepted_files == 27 and
    .coverage.accepted_declarations == 247 and
    .coverage.translated_but_not_certified == 0' \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_all_module_status.json" >/dev/null
  jq -e '.FILE_DAG_READY == true and .public_declarations == 5' \
    "$VALIDATION_ROOT/planning/v06_pipeline/model_processor_supply_selection.json" >/dev/null
  if rg -n '\b(sorry|axiom|unsafe)\b' \
      "$PROJECT_ROOT/Prosa/Model/Processor/Supply.lean" \
      "$VALIDATION_ROOT/fixtures/translation_order/SupplyComputationInterface.lean"; then
    echo "forbidden Lean proof escape in Supply snapshot" >&2
    return 1
  fi

  local module
  local util_modules=(
    Tactics Notation Rel Seqset Subadditivity Supremum Nat UnitGrowth
    SearchArg List Sum Epsilon Bigop Setoid Poet Bigcat Minmax Div_mod
    Nondecreasing All
  )
  for module in "${util_modules[@]}"; do
    validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Util/$module" \
      > "$VALIDATION_RUN_LOG/fresh_${module}.log" 2>&1
  done
  for module in Time Job Arrival_sequence Schedule; do
    validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Behavior/$module" \
      > "$VALIDATION_RUN_LOG/fresh_${module}.log" 2>&1
  done
  validation_compile_lean_module "$VALIDATION_PREPARED" \
    "Prosa/Model/Processor/Supply" \
    > "$VALIDATION_RUN_LOG/fresh_Supply.log" 2>&1

  mkdir -p "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order"
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ScheduleComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/ScheduleComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_schedule_interface.log" 2>&1
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/SupplyComputationInterface.olean" \
    "$VALIDATION_ROOT/fixtures/translation_order/SupplyComputationInterface.lean" \
    > "$VALIDATION_RUN_LOG/fresh_supply_interface.log" 2>&1
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    "$VALIDATION_ROOT/fixtures/translation_order/LeanSupplyAudit.lean" \
    > "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" 2>&1
  cp "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    "$VALIDATION_RUN_LOG/lean_freeze_and_axioms.log"
  python3 "$VALIDATION_ROOT/scripts/audit_lean_axioms.py" \
    --config "$VALIDATION_ROOT/fixtures/translation_order/supply_lean_axiom_config.json" \
    --log "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    --output "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    > "$VALIDATION_RUN_LOG/lean_axiom_classifier.log"
  jq -e '(.missing | length) == 0 and (.extra | length) == 0 and
    (.declarations | length) == 17 and
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
if len(files) != 27:
    raise SystemExit(f"expected 27 freshly compiled modules, found {len(files)}")
output.write_text(json.dumps({
    "status": "PASS",
    "mode": "FRESH_ACCEPTED_DEPENDENCY_CLOSURE_PLUS_SUPPLY_AND_INTERFACES",
    "module_count": len(files),
    "modules": {str(p.relative_to(root)): {
        "sha256": sha(p), "bytes": p.stat().st_size} for p in files},
}, indent=2, sort_keys=True) + "\n")
PY
  VALIDATION_STAGE_OUTPUTS=(
    "util_all_olean=$VALIDATION_PREPARED/olean/Prosa/Util/All.olean"
    "schedule_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Schedule.olean"
    "supply_olean=$VALIDATION_PREPARED/olean/Prosa/Model/Processor/Supply.olean"
    "schedule_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/ScheduleComputationInterface.olean"
    "supply_interface_olean=$VALIDATION_PREPARED/olean/Validation/fixtures/translation_order/SupplyComputationInterface.olean"
    "lean_axiom_summary=$VALIDATION_PREPARED/lean_axiom_summary.json"
    "dependency_build_manifest=$VALIDATION_PREPARED/dependency_build_manifest.json"
  )
}

validation_prepare_source_acquisition() {
  mkdir -p "$VALIDATION_PREPARED/source/util" \
    "$VALIDATION_PREPARED/source/behavior" \
    "$VALIDATION_PREPARED/source/model/processor"
  cp "$VALIDATION_ROOT/fixtures/translation_order/source_compat/arrival_sequence/util/all.v" \
    "$VALIDATION_PREPARED/source/util/all.v"
  cp "$SOURCE_ROOT/util/notation.v" "$VALIDATION_PREPARED/source/util/notation.v"
  local source
  for source in time job arrival_sequence schedule; do
    cp "$SOURCE_ROOT/behavior/${source}.v" \
      "$VALIDATION_PREPARED/source/behavior/${source}.v"
    cmp -s "$SOURCE_ROOT/behavior/${source}.v" \
      "$VALIDATION_PREPARED/source/behavior/${source}.v"
  done
  cp "$SOURCE_ROOT/model/processor/supply.v" \
    "$VALIDATION_PREPARED/source/model/processor/supply.v"
  cmp -s "$SOURCE_ROOT/model/processor/supply.v" \
    "$VALIDATION_PREPARED/source/model/processor/supply.v"
  [[ $(validation_sha256 "$VALIDATION_PREPARED/source/model/processor/supply.v") == \
    30264b6e8eb3055ef892c0456c889df7a8830847e64cd7f2da168835e8a79108 ]]
  if rg -n '^(Definition|Class|Record|Structure|Inductive|Variant|Lemma|Theorem|Fact|Remark)\b' \
      "$VALIDATION_PREPARED/source/util/all.v"; then
    echo "Supply compatibility interface declares a Prosa symbol" >&2
    return 1
  fi

  ulimit -s 65520
  for source in util/all.v util/notation.v behavior/time.v behavior/job.v \
      behavior/arrival_sequence.v behavior/schedule.v \
      model/processor/supply.v; do
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
expected = ["supply_at", "supply_during", "has_supply", "is_blackout",
            "blackout_during"]
rows = [r for r in csv.DictReader(
    (validation / "planning/v06_dependency/declaration_inventory.csv").open()
) if r["source_file"] == "model/processor/supply.v"]
if [r["declaration_name"] for r in rows] != expected:
    raise SystemExit("authoritative Supply inventory changed")
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
    "source_file": "model/processor/supply.v",
    "authoritative_source_sha256": sha(source_root / "model/processor/supply.v"),
    "compiled_source_sha256": sha(output_root / "model/processor/supply.v"),
    "byte_identical_authoritative_source": True,
    "compatibility_interface": "util/all.v",
    "compatibility_interface_sha256": sha(output_root / "util/all.v"),
    "compatibility_interface_declares_no_prosa_symbol": True,
    "declarations": declarations,
}
(output_root / "supply_source_acquisition.json").write_text(
    json.dumps(result, indent=2, sort_keys=True) + "\n")
PY
  VALIDATION_STAGE_OUTPUTS=(
    "source_compat=$VALIDATION_PREPARED/source/util/all.vo"
    "source_notation=$VALIDATION_PREPARED/source/util/notation.vo"
    "source_time=$VALIDATION_PREPARED/source/behavior/time.vo"
    "source_job=$VALIDATION_PREPARED/source/behavior/job.vo"
    "source_arrival=$VALIDATION_PREPARED/source/behavior/arrival_sequence.vo"
    "source_schedule=$VALIDATION_PREPARED/source/behavior/schedule.vo"
    "source_supply=$VALIDATION_PREPARED/source/model/processor/supply.vo"
    "source_metadata=$VALIDATION_PREPARED/source/supply_source_acquisition.json"
  )
}

validation_prepare_export() {
  "$VALIDATION_ROOT/scripts/export_actual_artifact.sh" \
    --config "$VALIDATION_ROOT/tooling/model_processor_supply_export_config.json" \
    --output "$VALIDATION_PREPARED/imported/Supply.out" \
    --log "$VALIDATION_RUN_LOG/export.log" \
    --metadata "$VALIDATION_PREPARED/imported/supply_export_metadata.json"
  VALIDATION_STAGE_OUTPUTS=(
    "export=$VALIDATION_PREPARED/imported/Supply.out"
    "export_metadata=$VALIDATION_PREPARED/imported/supply_export_metadata.json"
  )
}

validation_prepare_rocq_import() {
  cp "$VALIDATION_ROOT/imported/foundation_slice_2/Subadditivity.out" \
    "$VALIDATION_PREPARED/imported/Subadditivity.out"
  cp "$VALIDATION_ROOT/imported/foundation_slice_2/ImportedSubadditivity.v" \
    "$VALIDATION_PREPARED/imported/ImportedSubadditivity.v"
  cp "$VALIDATION_ROOT/fixtures/translation_order/ImportedSupply.v" \
    "$VALIDATION_PREPARED/imported/ImportedSupply.v"
  ulimit -s 65520
  local module
  for module in ImportedSubadditivity ImportedSupply; do
    (cd "$VALIDATION_PREPARED/imported" && \
      validation_rocq_compile "$VALIDATION_PREPARED" "${module}.v") \
      > "$VALIDATION_RUN_LOG/import_${module}.log" 2>&1
  done
  VALIDATION_STAGE_OUTPUTS=(
    "subadditivity_export=$VALIDATION_PREPARED/imported/Subadditivity.out"
    "subadditivity_import_vo=$VALIDATION_PREPARED/imported/ImportedSubadditivity.vo"
    "supply_import_source=$VALIDATION_PREPARED/imported/ImportedSupply.v"
    "supply_import_vo=$VALIDATION_PREPARED/imported/ImportedSupply.vo"
  )
}

validation_check_setup() {
  cp -R "$VALIDATION_PREPARED/olean/." "$VALIDATION_PHASE_WORK/olean/"
  cp -R "$VALIDATION_PREPARED/source/." "$VALIDATION_PHASE_WORK/source/"
  cp -R "$VALIDATION_PREPARED/imported/." "$VALIDATION_PHASE_WORK/imported/"
  cp "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    "$VALIDATION_PHASE_WORK/lean_axiom_summary.json"
}

validation_check_certificate_compile() {
  local common_dir="$VALIDATION_ROOT/certificates/common"
  local cert_dir="$VALIDATION_ROOT/certificates/model_processor_supply"
  mkdir -p "$VALIDATION_PHASE_WORK/certificates"
  cp "$common_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$cert_dir/"{SupplyScheduleOperations,SupplyNatBoolOperations,SupplyCorrespondence,SupplyImportedAudit,SupplySourceAudit,SupplyTypeAudit,SupplyAssumptionAudit}.v \
    "$VALIDATION_PHASE_WORK/certificates/"

  python3 "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py" \
    --template "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl" \
    --imported-module ImportedSupply --prefix sch --capital-prefix Sch \
    --imported-artifact "$VALIDATION_PHASE_WORK/imported/ImportedSupply.vo" \
    --output "$VALIDATION_PHASE_WORK/certificates/SupplyScheduleBaseAdapter.v" \
    --metadata "$VALIDATION_PHASE_WORK/certificates/supply_schedule_base_adapter.json" \
    --require-operation bool.roundtrip --require-operation bool.truth \
    --require-operation eqtype.decidable_eq \
    --require-operation list.roundtrip --require-operation list.membership
  cmp -s "$cert_dir/SupplyScheduleBaseAdapter.v" \
    "$VALIDATION_PHASE_WORK/certificates/SupplyScheduleBaseAdapter.v"
  python3 "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py" \
    --template "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl" \
    --imported-module ImportedSupply --prefix svc --capital-prefix Svc \
    --imported-artifact "$VALIDATION_PHASE_WORK/imported/ImportedSupply.vo" \
    --output "$VALIDATION_PHASE_WORK/certificates/SupplyBaseAdapter.v" \
    --metadata "$VALIDATION_PHASE_WORK/certificates/supply_base_adapter.json" \
    --require-operation bool.roundtrip --require-operation bool.truth \
    --require-operation eqtype.decidable_eq \
    --require-operation list.roundtrip --require-operation list.membership
  cmp -s "$cert_dir/SupplyBaseAdapter.v" \
    "$VALIDATION_PHASE_WORK/certificates/SupplyBaseAdapter.v"

  python3 "$VALIDATION_ROOT/scripts/instantiate_schedule_correspondence.py" \
    --source-dir "$VALIDATION_ROOT/certificates/behavior_schedule" \
    --output-dir "$VALIDATION_PHASE_WORK/certificates" \
    --imported-module ImportedSupply \
    --imported-artifact "$VALIDATION_PHASE_WORK/imported/ImportedSupply.v" \
    --target-prefix Supply --module ScheduleFiniteOperations \
    --metadata "$VALIDATION_PHASE_WORK/certificates/supply_schedule_instantiation.json"
  cmp -s "$cert_dir/SupplyScheduleFiniteOperations.v" \
    "$VALIDATION_PHASE_WORK/certificates/SupplyScheduleFiniteOperations.v"
  python3 "$VALIDATION_ROOT/scripts/instantiate_service_correspondence.py" \
    --source-dir "$VALIDATION_ROOT/certificates/behavior_service" \
    --output-dir "$VALIDATION_PHASE_WORK/certificates" \
    --imported-module ImportedSupply \
    --imported-artifact "$VALIDATION_PHASE_WORK/imported/ImportedSupply.v" \
    --target-prefix Supply --module ServiceIntervalOperations \
    --metadata "$VALIDATION_PHASE_WORK/certificates/supply_interval_instantiation.json"
  cmp -s "$cert_dir/SupplyIntervalOperations.v" \
    "$VALIDATION_PHASE_WORK/certificates/SupplyIntervalOperations.v"

  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' \
      "$VALIDATION_PHASE_WORK/certificates" --glob '*.v' \
      --glob '!PropSPropFoundation.v'; then
    echo "forbidden Supply certificate proof escape" >&2
    return 1
  fi
  ulimit -s 65520
  local module
  for module in PropSPropFoundation LogicalRelation \
      SubadditivityNatCorrespondence SupplyScheduleBaseAdapter \
      SupplyScheduleFiniteOperations SupplyScheduleOperations \
      SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations \
      SupplyCorrespondence SupplyImportedAudit SupplySourceAudit \
      SupplyTypeAudit SupplyAssumptionAudit; do
    validation_rocq_compile "$VALIDATION_PHASE_WORK" \
      "$VALIDATION_PHASE_WORK/certificates/${module}.v" \
      > "$VALIDATION_RUN_LOG/rocq_${module}.log" 2>&1
  done
  cp "$VALIDATION_RUN_LOG/rocq_SupplyAssumptionAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  cat "$VALIDATION_RUN_LOG/rocq_SupplyScheduleBaseAdapter.log" \
      "$VALIDATION_RUN_LOG/rocq_SupplyScheduleFiniteOperations.log" \
      "$VALIDATION_RUN_LOG/rocq_SupplyScheduleOperations.log" \
      "$VALIDATION_RUN_LOG/rocq_SupplyBaseAdapter.log" \
      "$VALIDATION_RUN_LOG/rocq_SupplyNatBoolOperations.log" \
      "$VALIDATION_RUN_LOG/rocq_SupplyIntervalOperations.log" \
    > "$VALIDATION_PHASE_WORK/certificates/adapter_assumptions.log"
  cp "$VALIDATION_RUN_LOG/rocq_SupplyTypeAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/type_audit.log"
  VALIDATION_STAGE_OUTPUTS=(
    "schedule_adapter_metadata=$VALIDATION_PHASE_WORK/certificates/supply_schedule_base_adapter.json"
    "supply_adapter_metadata=$VALIDATION_PHASE_WORK/certificates/supply_base_adapter.json"
    "schedule_instantiation=$VALIDATION_PHASE_WORK/certificates/supply_schedule_instantiation.json"
    "interval_instantiation=$VALIDATION_PHASE_WORK/certificates/supply_interval_instantiation.json"
    "correspondence_vo=$VALIDATION_PHASE_WORK/certificates/SupplyCorrespondence.vo"
    "type_audit_vo=$VALIDATION_PHASE_WORK/certificates/SupplyTypeAudit.vo"
    "assumption_audit_vo=$VALIDATION_PHASE_WORK/certificates/SupplyAssumptionAudit.vo"
    "type_audit_log=$VALIDATION_PHASE_WORK/certificates/type_audit.log"
    "assumption_log=$VALIDATION_PHASE_WORK/certificates/assumptions.log"
    "adapter_assumption_log=$VALIDATION_PHASE_WORK/certificates/adapter_assumptions.log"
  )
}

validation_check_assumption_audit() {
  local cert_dir="$VALIDATION_ROOT/certificates/model_processor_supply"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$cert_dir/supply_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/assumption_classifier.log"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$cert_dir/supply_adapter_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/adapter_assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/adapter_assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/adapter_assumption_classifier.log"
  jq -e '
    (.certificates | length) == 6 and
    ([.certificates[] | select(.status == "CERTIFIED")] | length) == 3 and
    ([.certificates[] | select(.status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")] | length) == 3 and
    ([.certificates[] |
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all)' \
    "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" >/dev/null
  jq -e '
    (.certificates | length) == 17 and
    ([.certificates[] |
      (.status == "CERTIFIED" or
       .status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION") and
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all)' \
    "$VALIDATION_PHASE_WORK/certificates/adapter_assumption_summary.json" >/dev/null
  python3 - \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_all_module_status.json" \
    "$VALIDATION_PHASE_WORK/certificates/baseline_after.json" <<'PY'
import json, sys
from pathlib import Path
source, output = map(Path, sys.argv[1:])
data = json.loads(source.read_text())
ok = (data.get("status") == "PASS"
      and data["coverage"]["accepted_files"] == 27
      and data["coverage"]["accepted_declarations"] == 247
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
  local publish_dir="$VALIDATION_ROOT/imported/translation_order/supply"
  local pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
  local report="$PROJECT_ROOT/Reports/files/model/processor/2026-09-23_055700_supply.md"
  local run_report="$PROJECT_ROOT/Reports/runs/2026-09-22_000308_translation_order_continuous_run.md"
  mkdir -p "$publish_dir" "$(dirname "$report")"
  cp "$VALIDATION_PHASE_WORK/imported/"{Supply.out,ImportedSupply.v,ImportedSupply.vo} \
    "$publish_dir/"
  local module
  for module in SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations \
      SupplyScheduleOperations SupplyBaseAdapter SupplyNatBoolOperations \
      SupplyIntervalOperations SupplyCorrespondence SupplyImportedAudit \
      SupplySourceAudit SupplyTypeAudit SupplyAssumptionAudit; do
    cp "$VALIDATION_PHASE_WORK/certificates/${module}.vo" \
      "$publish_dir/${module}.vo"
  done
  cp "$VALIDATION_PHASE_WORK/certificates/"{supply_schedule_base_adapter.json,supply_base_adapter.json,supply_schedule_instantiation.json,supply_interval_instantiation.json,assumption_summary.json,adapter_assumption_summary.json} \
    "$publish_dir/"
  cp "$VALIDATION_PHASE_WORK/lean_axiom_summary.json" "$publish_dir/"
  cp "$VALIDATION_PHASE_WORK/source/supply_source_acquisition.json" "$publish_dir/"

  python3 "$VALIDATION_ROOT/scripts/publish_model_processor_supply.py" \
    --project "$PROJECT_ROOT" --source "$SOURCE_ROOT" \
    --work "$VALIDATION_PHASE_WORK" \
    --prepare-evidence "$VALIDATION_PREPARE_EVIDENCE" \
    --snapshot-id "$VALIDATION_SNAPSHOT_ID" \
    --previous-status "$pipeline_dir/behavior_all_module_status.json" \
    --manifest-output "$pipeline_dir/model_processor_supply_module_manifest.json" \
    --status-output "$pipeline_dir/model_processor_supply_module_status.json" \
    --canonical-report "$report" --run-report "$run_report"
  (cd "$REPO_ROOT" && git diff --check)
  VALIDATION_STAGE_OUTPUTS=(
    "module_manifest=$pipeline_dir/model_processor_supply_module_manifest.json"
    "module_status=$pipeline_dir/model_processor_supply_module_status.json"
    "canonical_report=$report"
    "published_import=$publish_dir/ImportedSupply.vo"
    "published_certificate=$publish_dir/SupplyCorrespondence.vo"
  )
}
