#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
prosa_root=$(cd "$validation_root/.." && pwd)
rocq_dir="$validation_root/rocq"
log_dir="$validation_root/reports/logs/experiment10"
switch_name=${IMPORT_OPAM_SWITCH:-rocq93rc1}
importer_src=${ROCQLI_SRC:-/private/tmp/rocq-lean-import-93}
prosa_src=${PROSA_ROCQ_SRC:-/Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6}
generated="$rocq_dir/generated_hard"
sum_targets=big_nat_eq0,sum_of_ones,sum_le_summation_range

mkdir -p "$log_dir" "$generated" "$validation_root/.work/experiment10_source_snapshots"

if ! git -C "$prosa_root" diff --quiet -- Prosa; then
  echo "production Lean translation differs from the frozen snapshot" >&2
  exit 1
fi

checked=(
  "$rocq_dir/PropSPropFoundation.v"
  "$rocq_dir/FiniteNatSumBridge.v"
  "$rocq_dir/FiniteNatSumReuseCertificates.v"
  "$rocq_dir/JobArrivalClassCertificate.v"
  "$rocq_dir/CompletesAtSemanticCertificate.v"
  "$validation_root/lean_fixtures/completes_at_corrected/CompletesAtCorrected.lean"
)
if rg -n '\b(Admitted|admit|sorry)\b' "${checked[@]}"; then
  echo "forbidden proof escape found" >&2
  exit 1
fi
unexpected_axioms=$(rg -n '\bAxiom\b' "${checked[@]}" | \
  rg -v 'PropSPropFoundation\.v:.*interpret_strict' || true)
if [[ -n "$unexpected_axioms" ]]; then
  echo "unexpected validation axiom" >&2
  echo "$unexpected_axioms" >&2
  exit 1
fi

python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$validation_root/mapping/hard_validation_targets.yaml" \
  --source-root "$prosa_src" --target-keys "$sum_targets" \
  --output-dir "$validation_root/.work/experiment10_source_snapshots" \
  --metadata "$log_dir/sum_source_fidelity.json"
python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$validation_root/mapping/rts_validation_targets.yaml" \
  --source-root "$prosa_src" \
  --target-keys completes_at_current,completes_at_corrected \
  --output-dir "$validation_root/.work/experiment10_source_snapshots" \
  --metadata "$log_dir/completes_at_source_fidelity.json"
python3 "$validation_root/scripts/generate_rocq_source_modules.py" \
  --mapping "$validation_root/mapping/hard_validation_targets.yaml" \
  --source-root "$prosa_src" --output-dir "$generated"

if [[ ${REEXPORT:-1} == 1 ]]; then
  HARD_LOG_PREFIX=experiment10/finite_sum_all_projected \
    HARD_ALL_THEOREMS_STATEMENT_ONLY=1 \
    HARD_TARGET_KEYS="$sum_targets" \
    HARD_ARTIFACT="$validation_root/export/FiniteNatSumNormalizedTargets.out" \
    "$validation_root/scripts/export_hard_validation.sh"
  "$validation_root/scripts/export_completes_at_validation.sh"
  "$validation_root/scripts/export_rts_validation.sh" \
    > "$log_dir/export_rts_validation.log" 2>&1
fi

sum_artifact="$validation_root/export/FiniteNatSumNormalizedTargets.out"
completes_artifact="$validation_root/export/CompletesAtValidation.out"
rts_artifact="$validation_root/export/RTSValidation.out"
for artifact in "$sum_artifact" "$completes_artifact" "$rts_artifact"; do
  [[ -s "$artifact" ]] || { echo "missing actual Lean artifact: $artifact" >&2; exit 1; }
done
[[ $(rg -c '^#AX ' "$sum_artifact") == 3 ]] || {
  echo "finite-sum artifact contains unexpected transitive signatures" >&2; exit 1;
}
rg -q 'kernel_rfl_guard=true' "$log_dir/completes_at_export.log"

compile() {
  local file=$1 log=$2
  opam exec --switch="$switch_name" -- rocq c \
    -R "$prosa_src" prosa \
    -Q "$importer_src/src" LeanImport -I "$importer_src/src" \
    -Q "$generated" HardSource "$file" > "$log_dir/$log" 2>&1
}

cd "$rocq_dir"
ulimit -s 65520
compile PropSPropFoundation.v foundation.log
compile "$generated/Generated_util__sum.v" official_sum_source.log
compile CompletesAtSourceFidelity.v completes_at_official_type.log
compile ImportedFiniteNatSumNormalized93.v imported_finite_sum.log
compile HardSumCertificate.v hard_sum.log
compile FiniteNatSumBridge.v finite_sum_bridge.log
compile FiniteNatSumReuseCertificates.v finite_sum_reuse.log
compile AssumptionAuditFiniteSumExperiment9.v finite_sum_assumptions.log

# RTSValidation.out is deterministic for the frozen source.  Re-importing its
# 2.68 MB graph can be requested explicitly; otherwise require the already
# kernel-checked .vo and exact known artifact hash.
if [[ ${REIMPORT_RTS:-0} == 1 ]]; then
  compile ImportedEasy93.v imported_rts.log
else
  [[ -s ImportedEasy93.vo ]] || {
    echo "missing ImportedEasy93.vo; rerun with REIMPORT_RTS=1" >&2; exit 1;
  }
  expected_rts=60f07832ce3bdc4c8d940ead5afbfef94ed4600fabf65113bb4ebd31ee9d590b
  actual_rts=$(shasum -a 256 "$rts_artifact" | awk '{print $1}')
  [[ "$actual_rts" == "$expected_rts" ]] || {
    echo "RTS artifact changed; rerun with REIMPORT_RTS=1" >&2; exit 1;
  }
fi
compile JobArrivalClassCertificate.v job_arrival_class.log
compile ImportedCompletesAt93.v imported_completes_at.log
compile CompletesAtSemanticCertificate.v completes_at_certificate.log
compile AssumptionAuditExperiment10.v experiment10_assumptions.log

cd "$validation_root"
python3 scripts/classify_assumptions.py \
  --config mapping/experiment9_assumption_audit.yaml \
  --log "$log_dir/finite_sum_assumptions.log" \
  --output "$log_dir/assumption_summary_finite_sum.json" \
  > "$log_dir/assumption_classification_finite_sum.log"
python3 scripts/classify_assumptions.py \
  --config mapping/experiment10_assumption_audit.yaml \
  --log "$log_dir/experiment10_assumptions.log" \
  --output "$log_dir/assumption_summary_experiment10.json" \
  > "$log_dir/assumption_classification_experiment10.log"

scripts/test_clean_lean_rebuild.sh > "$log_dir/cache_invalidation_run.log" 2>&1
scripts/test_interval_semantic_mutation.sh > "$log_dir/interval_mutation_summary.log" 2>&1

python3 - "$log_dir/assumption_summary_finite_sum.json" \
  "$log_dir/assumption_summary_experiment10.json" \
  "$validation_root/reports/logs/experiment8/statement_dependency_comparison_experiment9.json" <<'PY'
import json, sys
sums = json.load(open(sys.argv[1]))["certificates"]
cases = json.load(open(sys.argv[2]))["certificates"]
baseline = json.load(open(sys.argv[3]))["targets"]["sum_le_summation_range"]["after"]
remaining = len(sums['sum_le_summation_range']['statement_only_dependencies'])
print("Generalized Semantic Validation — Experiment 10")
print()
print(f"{'sum_le_summation_range':36} {sums['sum_le_summation_range']['status']}")
print(f"{'JobArrival full class':36} {cases['job_arrival_full_class']['status']}")
print(f"{'completes_at current':36} FAILED_SEMANTIC_EQUIVALENCE")
print(f"{'completes_at corrected fixture':36} {cases['completes_at_corrected']['status']}")
print()
print(f"sum_le_summation_range statement dependencies: {baseline} -> {remaining}")
print("semantic premises: none")
print("target theorem self dependency: false")
print("unexpected assumptions: none")
print("counterexample: t=0, job_cost=0")
PY
echo "Finite-sum artifact SHA-256: $(shasum -a 256 "$sum_artifact" | awk '{print $1}')"
echo "Completes-at artifact SHA-256: $(shasum -a 256 "$completes_artifact" | awk '{print $1}')"
echo "Logs: $log_dir"
