#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
rocq_dir="$validation_root/rocq"
log_dir="$validation_root/reports/logs"
experiment_log_dir="$log_dir/experiment8"
mapping="$validation_root/mapping/hard_validation_targets.yaml"
switch_name=${IMPORT_OPAM_SWITCH:-rocq93rc1}
importer_src=${ROCQLI_SRC:-/private/tmp/rocq-lean-import-93}
prosa_src=${PROSA_ROCQ_SRC:-/Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6}
generated="$rocq_dir/generated_hard"
targets='big_nat_eq0,sum_of_ones,sum_le_summation_range'

mkdir -p "$log_dir" "$experiment_log_dir" "$generated" \
  "$validation_root/.work/experiment9_source_snapshots"

if ! git -C "$validation_root/.." diff --quiet -- Prosa; then
  echo "production Lean translation differs from the frozen snapshot" >&2
  exit 1
fi

python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root "$prosa_src" --target-keys "$targets" \
  --output-dir "$validation_root/.work/experiment9_source_snapshots" \
  --metadata "$experiment_log_dir/source_extraction.json"
python3 "$validation_root/scripts/generate_rocq_source_modules.py" \
  --mapping "$mapping" --source-root "$prosa_src" --output-dir "$generated"

if [[ ${REEXPORT:-0} == 1 ]]; then
  HARD_LOG_PREFIX=experiment8/experiment9_normalized_simple HARD_ALL_THEOREMS_STATEMENT_ONLY=1 \
    HARD_TARGET_KEYS='big_nat_eq0,sum_of_ones' \
    HARD_ARTIFACT="$validation_root/export/FiniteNatSumNormalizedSimpleTargets.out" \
    "$validation_root/scripts/export_hard_validation.sh"
  HARD_LOG_PREFIX=experiment8/experiment9_sum_le_fallback HARD_ALL_THEOREMS_STATEMENT_ONLY=1 \
    HARD_BODY_THEOREMS="$(sed '/^#/d;/^$/d' \
      "$validation_root/mapping/finite_sum_fallback_body_theorems.txt")" \
    HARD_TARGET_KEYS='sum_le_summation_range' \
    HARD_ARTIFACT="$validation_root/export/FiniteNatSumTargets.out" \
    "$validation_root/scripts/export_hard_validation.sh"
fi

normalized_artifact="$validation_root/export/FiniteNatSumNormalizedSimpleTargets.out"
fallback_artifact="$validation_root/export/FiniteNatSumTargets.out"
for artifact in "$normalized_artifact" "$fallback_artifact"; do
  [[ -s "$artifact" ]] || {
    echo "missing actual Lean artifact: $artifact (run with REEXPORT=1)" >&2
    exit 1
  }
done

checked=(PropSPropFoundation.v PropSPropBridge.v ImportedFiniteNatSumNormalized93.v \
  ImportedBigNatEq093.v HardSumCertificate.v FiniteNatSumBridge.v \
  FiniteNatSumReuseCertificates.v HardSumMutationTest.v \
  AssumptionAuditFiniteSumExperiment9.v)
if rg -n '\b(Admitted|admit|sorry)\b' "${checked[@]/#/$rocq_dir/}"; then
  echo "forbidden proof escape found" >&2
  exit 1
fi
unexpected_axioms=$(rg -n '\bAxiom\b' "${checked[@]/#/$rocq_dir/}" | \
  rg -v 'PropSPropFoundation\.v:.*interpret_strict' || true)
if [[ -n "$unexpected_axioms" ]]; then
  echo "unexpected validation axiom" >&2
  echo "$unexpected_axioms" >&2
  exit 1
fi

compile() {
  local file=$1 log=$2
  opam exec --switch="$switch_name" -- rocq c \
    -R "$prosa_src" prosa \
    -Q "$importer_src/src" LeanImport -I "$importer_src/src" \
    -Q "$generated" HardSource "$file" > "$log_dir/$log" 2>&1
}

cd "$rocq_dir"
ulimit -s 65520
compile PropSPropFoundation.v experiment7_validate_PropSPropFoundation.log
compile PropSPropBridge.v experiment7_validate_PropSPropBridge.log
compile "$generated/Generated_util__sum.v" experiment6_validate_official_sum_source.log
compile ImportedFiniteNatSumNormalized93.v experiment8/experiment9_validate_normalized_actual_artifact.log
compile ImportedBigNatEq093.v experiment6_validate_actual_sum_artifact.log
compile HardSumCertificate.v experiment6_validate_HardSumCertificate.log
compile FiniteNatSumBridge.v experiment6_validate_FiniteNatSumBridge.log
compile FiniteNatSumReuseCertificates.v experiment6_validate_FiniteNatSumReuseCertificates.log
compile HardSumMutationTest.v experiment6_validate_HardSumMutationTest.log
compile AssumptionAuditFiniteSumExperiment9.v experiment8/experiment9_assumptions.log

cd "$validation_root/.."

python3 "$validation_root/scripts/classify_assumptions.py" \
  --config "$validation_root/mapping/experiment9_assumption_audit.yaml" \
  --log "$experiment_log_dir/experiment9_assumptions.log" \
  --output "$experiment_log_dir/assumption_summary_experiment9.json" \
  | tee "$experiment_log_dir/assumption_classification_experiment9.log"
python3 "$validation_root/scripts/compare_statement_dependencies.py" \
  --before "$experiment_log_dir/baseline_assumption_summary.json" \
  --after "$experiment_log_dir/assumption_summary_experiment9.json" \
  --json "$experiment_log_dir/statement_dependency_comparison_experiment9.json" \
  --markdown "$experiment_log_dir/statement_dependency_comparison_experiment9.md"
python3 "$validation_root/scripts/classify_statement_dependency_reduction.py" \
  --before "$experiment_log_dir/baseline_assumption_summary.json" \
  --after "$experiment_log_dir/assumption_summary_experiment9.json" \
  --body-theorems "$validation_root/mapping/finite_sum_fallback_body_theorems.txt" \
  --json "$experiment_log_dir/dependency_classification_experiment9.json" \
  --markdown "$experiment_log_dir/dependency_classification_experiment9.md"

python3 "$validation_root/scripts/audit_source_fidelity.py" \
  --mapping "$mapping" --source-root "$prosa_src" --generated-dir "$generated" \
  --output "$experiment_log_dir/source_fidelity_audit.json" \
  > "$experiment_log_dir/source_fidelity_audit.log"

"$validation_root/scripts/test_clean_lean_rebuild.sh" \
  > "$experiment_log_dir/cache_invalidation_run.log" 2>&1
"$validation_root/scripts/test_interval_semantic_mutation.sh" \
  > "$experiment_log_dir/interval_mutation_summary.log" 2>&1

echo "Finite Nat Sum Semantic Validation — Experiment 9"
echo
python3 - "$experiment_log_dir/assumption_summary_experiment9.json" <<'PY'
import json, sys
for key, value in json.load(open(sys.argv[1]))["certificates"].items():
    print(f"{key:32} {value['status']}")
PY
echo
echo "Validation-specific premises: none"
echo "Mutation: sum = 0 -> sum = 1   PASS (closed certificate rejected)"
echo "End-to-end endpoint mutation:  PASS"
echo "Normalized artifact SHA-256: $(shasum -a 256 "$normalized_artifact" | awk '{print $1}')"
echo "Fallback artifact SHA-256:   $(shasum -a 256 "$fallback_artifact" | awk '{print $1}')"
cat "$experiment_log_dir/statement_dependency_comparison_experiment9.md"
echo "Logs: $experiment_log_dir"
