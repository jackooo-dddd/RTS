#!/usr/bin/env bash

# Regression hooks for the generic incremental driver.  The three accepted
# samples exercise sequence/sum normalization history, ordinary theorem
# statements, and universe-sensitive List/Bool adapters.

VALIDATION_PREPARE_INPUTS=(
  "$VALIDATION_ROOT/tooling/workflow_regression_descriptor.json"
)
VALIDATION_CHECK_INPUTS=(
  "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl"
  "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py"
  "$VALIDATION_ROOT/scripts/audit_assumptions.py"
  "$VALIDATION_ROOT/tooling/workflow_adapter_assumption_config.json"
  "$VALIDATION_ROOT/certificates/common/PropSPropFoundation.v"
  "$VALIDATION_ROOT/certificates/common/LogicalRelation.v"
  "$VALIDATION_ROOT/certificates/common/SubadditivityNatCorrespondence.v"
)

validation_prepare_lean_build() {
  mkdir -p "$VALIDATION_PREPARED/olean/Prosa/Util"
  local module
  for module in Tactics Supremum List Notation Rel Nat Sum Poet Bigcat; do
    validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Util/$module" \
      > "$VALIDATION_RUN_LOG/fresh_${module}.log" 2>&1
  done
  VALIDATION_STAGE_OUTPUTS=(
    "sum_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Sum.olean"
    "poet_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Poet.olean"
    "bigcat_olean=$VALIDATION_PREPARED/olean/Prosa/Util/Bigcat.olean"
  )
}

validation_prepare_source_acquisition() {
  mkdir -p "$VALIDATION_PREPARED/source/util"
  cp "$SOURCE_ROOT/util/sum.v" "$VALIDATION_PREPARED/source/util/sum.v"
  cp "$SOURCE_ROOT/util/poet.v" "$VALIDATION_PREPARED/source/util/poet.v"
  cp "$SOURCE_ROOT/util/bigcat.v" "$VALIDATION_PREPARED/source/util/bigcat.v"
  VALIDATION_STAGE_OUTPUTS=(
    "sum_source=$VALIDATION_PREPARED/source/util/sum.v"
    "poet_source=$VALIDATION_PREPARED/source/util/poet.v"
    "bigcat_source=$VALIDATION_PREPARED/source/util/bigcat.v"
  )
}

validation_prepare_export() {
  # These are accepted, content-addressed historical outputs.  This
  # regression verifies reuse; it does not mislabel the copies as fresh
  # exporter executions.
  mkdir -p "$VALIDATION_PREPARED/imported"
  cp "$VALIDATION_ROOT/imported/utility_foundation/SumSequence.out" \
    "$VALIDATION_PREPARED/imported/SumSequence.out"
  cp "$VALIDATION_ROOT/imported/translation_order/poet/Poet.out" \
    "$VALIDATION_PREPARED/imported/Poet.out"
  cp "$VALIDATION_ROOT/imported/translation_order/bigcat/Bigcat.out" \
    "$VALIDATION_PREPARED/imported/Bigcat.out"
  VALIDATION_STAGE_MODE=VERIFIED_CACHE
  VALIDATION_STAGE_EXECUTED=false
  VALIDATION_STAGE_OUTPUTS=(
    "sum_export=$VALIDATION_PREPARED/imported/SumSequence.out"
    "poet_export=$VALIDATION_PREPARED/imported/Poet.out"
    "bigcat_export=$VALIDATION_PREPARED/imported/Bigcat.out"
  )
}

validation_prepare_rocq_import() {
  cp "$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo" \
    "$VALIDATION_PREPARED/imported/ImportedSubadditivity.vo"
  cp "$VALIDATION_ROOT/imported/utility_foundation/ImportedSumSequence.vo" \
    "$VALIDATION_PREPARED/imported/ImportedSumSequence.vo"
  cp "$VALIDATION_ROOT/imported/translation_order/poet/ImportedPoet.vo" \
    "$VALIDATION_PREPARED/imported/ImportedPoet.vo"
  cp "$VALIDATION_ROOT/imported/translation_order/bigcat/ImportedBigcat.vo" \
    "$VALIDATION_PREPARED/imported/ImportedBigcat.vo"
  VALIDATION_STAGE_MODE=VERIFIED_CACHE
  VALIDATION_STAGE_EXECUTED=false
  VALIDATION_STAGE_OUTPUTS=(
    "subadd_import=$VALIDATION_PREPARED/imported/ImportedSubadditivity.vo"
    "sum_import=$VALIDATION_PREPARED/imported/ImportedSumSequence.vo"
    "poet_import=$VALIDATION_PREPARED/imported/ImportedPoet.vo"
    "bigcat_import=$VALIDATION_PREPARED/imported/ImportedBigcat.vo"
  )
}

validation_check_setup() {
  cp -R "$VALIDATION_PREPARED/olean/." "$VALIDATION_PHASE_WORK/olean/"
  cp -R "$VALIDATION_PREPARED/source/." "$VALIDATION_PHASE_WORK/source/"
  cp -R "$VALIDATION_PREPARED/imported/." "$VALIDATION_PHASE_WORK/imported/"
  cp "$VALIDATION_ROOT/certificates/common/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
}

validation_check_certificate_compile() {
  local module imported prefix cap
  for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    (cd "$VALIDATION_PHASE_WORK/certificates" && \
      validation_rocq_compile "$VALIDATION_PHASE_WORK" "$module.v") \
      > "$VALIDATION_RUN_LOG/rocq_${module}.log" 2>&1
  done
  while read -r imported prefix cap; do
    python3 "$VALIDATION_ROOT/scripts/generate_artifact_bool_list_adapter.py" \
      --template "$VALIDATION_ROOT/templates/ArtifactBoolListAdapter.v.tpl" \
      --imported-module "$imported" --prefix "$prefix" \
      --imported-artifact "$VALIDATION_PHASE_WORK/imported/${imported}.vo" \
      --capital-prefix "$cap" \
      --output "$VALIDATION_PHASE_WORK/certificates/Generated${cap}Adapter.v" \
      --metadata "$VALIDATION_PHASE_WORK/certificates/Generated${cap}Adapter.json"
    (cd "$VALIDATION_PHASE_WORK/certificates" && \
      validation_rocq_compile "$VALIDATION_PHASE_WORK" "Generated${cap}Adapter.v") \
      > "$VALIDATION_RUN_LOG/rocq_Generated${cap}Adapter.log" 2>&1
  done <<'EOF'
ImportedPoet rp Rp
ImportedBigcat rb Rb
ImportedSumSequence rs Rs
EOF
  VALIDATION_STAGE_OUTPUTS=(
    "poet_adapter=$VALIDATION_PHASE_WORK/certificates/GeneratedRpAdapter.vo"
    "bigcat_adapter=$VALIDATION_PHASE_WORK/certificates/GeneratedRbAdapter.vo"
    "sum_adapter=$VALIDATION_PHASE_WORK/certificates/GeneratedRsAdapter.vo"
  )
}

validation_check_assumption_audit() {
  cat "$VALIDATION_RUN_LOG/rocq_GeneratedRpAdapter.log" \
      "$VALIDATION_RUN_LOG/rocq_GeneratedRbAdapter.log" \
      "$VALIDATION_RUN_LOG/rocq_GeneratedRsAdapter.log" \
      > "$VALIDATION_RUN_LOG/adapter_assumptions.log"
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$VALIDATION_ROOT/tooling/workflow_adapter_assumption_config.json" \
    --log "$VALIDATION_RUN_LOG/adapter_assumptions.log" \
    --output "$VALIDATION_RUN_LOG/adapter_assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/adapter_assumption_classifier.log"
  jq -e '[.certificates[] |
      (.semantic_premises | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false) and
      (.status == "CERTIFIED" or
       .status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION")] | all' \
    "$VALIDATION_RUN_LOG/adapter_assumption_summary.json" >/dev/null
  VALIDATION_STAGE_OUTPUTS=(
    "adapter_audit=$VALIDATION_RUN_LOG/adapter_assumption_summary.json"
  )
}

validation_finalize_publication() {
  local output="$VALIDATION_RUN_LOG/regression_result.json"
  python3 - "$VALIDATION_ROOT" "$VALIDATION_SNAPSHOT_ID" "$output" <<'PY'
import json, sys
from pathlib import Path

root, snapshot, output = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3])
load = lambda rel: json.loads((root / rel).read_text())

sum_status = load("planning/v06_pipeline/utility_foundation_expansion_status.json")
sum_row = sum_status["per_file"]["util/sum.v"]
assert sum_row["status"] == "ACCEPTED_V06_FILE"
assert sum_row["certified"] == 25
sum_results = [
    load("logs/utility_foundation_expansion/cluster_results/sum_interval.json"),
    load("logs/utility_foundation_expansion/cluster_results/sum_sequence.json"),
]
assert sum(len(x["declarations"]) for x in sum_results) == 25
assert all(row["acceptance"] == "ACCEPTED_V06_TRANSLATION"
           for result in sum_results for row in result["declarations"])

samples = {"sum": 25}
for name, expected in (("poet", 1), ("bigcat", 13)):
    status = load(f"planning/v06_pipeline/{name}_module_status.json")
    manifest = load(f"planning/v06_pipeline/{name}_module_manifest.json")
    result = load(f"logs/translation_order/cluster_results/{name}.json")
    assert status["status"] == "PASS"
    assert manifest["acceptance"] == "ACCEPTED_V06_FILE"
    assert len(manifest["declarations"]) == expected
    assert len(result["declarations"]) == expected
    assert all(row["acceptance"] == "ACCEPTED_V06_TRANSLATION"
               for row in result["declarations"])
    samples[name] = expected

output.write_text(json.dumps({
    "schema_version": 1,
    "snapshot_id": snapshot,
    "samples": samples,
    "semantic_results_changed": False,
    "acceptance_gate_changed": False,
    "regression_status": "PASS",
}, indent=2, sort_keys=True) + "\n")
PY
  VALIDATION_STAGE_OUTPUTS=("regression_result=$output")
}
