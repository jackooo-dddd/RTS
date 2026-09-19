#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
rocq_dir="$validation_root/rocq"
log_dir="$validation_root/reports/logs"
mapping="$validation_root/mapping/hard_validation_targets.yaml"
switch_name=${IMPORT_OPAM_SWITCH:-rocq93rc1}
importer_src=${ROCQLI_SRC:-/private/tmp/rocq-lean-import-93}
prosa_src=${PROSA_ROCQ_SRC:-/Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6}
generated="$rocq_dir/generated_hard"

mkdir -p "$log_dir" "$generated"

python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root "$prosa_src" \
  --output-dir "$validation_root/.work/hard_source_snapshots" \
  --metadata "$log_dir/experiment5_source_fidelity.json"
python3 "$validation_root/scripts/generate_rocq_source_modules.py" \
  --mapping "$mapping" --source-root "$prosa_src" --output-dir "$generated"

if [[ ${REEXPORT:-0} == 1 ]]; then
  HARD_TARGET_KEYS='rem_all,nin_rem_all,spin_processor_state,spin_scheduled_on' \
    HARD_ARTIFACT="$validation_root/export/HardCoreValidation.out" \
    "$validation_root/scripts/export_hard_validation.sh"
  HARD_TARGET_KEYS='exists_first_intermediate_point' \
    HARD_ARTIFACT="$validation_root/export/ExistsFirstIntermediatePoint.out" \
    "$validation_root/scripts/export_hard_validation.sh"
  HARD_ALL_THEOREMS_STATEMENT_ONLY=1 HARD_TARGET_KEYS='big_nat_eq0' \
    HARD_ARTIFACT="$validation_root/export/BigNatEq0AllStatements.out" \
    "$validation_root/scripts/export_hard_validation.sh"
fi

for artifact in HardCoreValidation.out ExistsFirstIntermediatePoint.out BigNatEq0AllStatements.out; do
  [[ -s "$validation_root/export/$artifact" ]] || {
    echo "missing validation artifact: $artifact (run with REEXPORT=1)" >&2
    exit 1
  }
done

checked_files=(
  PropSPropFoundation.v PropSPropBridge.v HardCoreCertificates.v HardNinRemAllCertificate.v
  HardStepFunctionCertificate.v HardSumCertificate.v HardSumMutationTest.v
)
if rg -n '\b(Admitted|admit|sorry)\b' \
    "${checked_files[@]/#/$rocq_dir/}"; then
  echo "forbidden proof escape found" >&2
  exit 1
fi
unexpected_axioms=$(rg -n '\bAxiom\b' "${checked_files[@]/#/$rocq_dir/}" | \
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
for source_module in Generated_util__list.v Generated_util__sum.v Generated_util__unit_growth.v; do
  compile "$generated/$source_module" "experiment5_validate_${source_module%.v}.log"
done
compile ImportedHardCore93.v experiment5_validate_ImportedHardCore93.log
compile HardCoreCertificates.v experiment5_validate_HardCoreCertificates.log
compile HardNinRemAllCertificate.v experiment5_validate_HardNinRemAllCertificate.log
compile ImportedExistsFirstIntermediatePoint93.v experiment5_validate_ImportedExistsFirstIntermediatePoint93.log
compile HardStepFunctionCertificate.v experiment5_validate_HardStepFunctionCertificate.log
compile ImportedBigNatEq093.v experiment5_validate_ImportedBigNatEq093.log
compile HardSumCertificate.v experiment5_validate_HardSumCertificate.log
compile FiniteNatSumBridge.v experiment7_validate_FiniteNatSumBridge.log
compile FiniteNatSumReuseCertificates.v experiment7_validate_FiniteNatSumReuseCertificates.log
compile HardSumMutationTest.v experiment5_validate_HardSumMutationTest.log

echo "Hard certificate compilation completed."
echo "Authoritative statuses are produced by classify_assumptions.py."
echo "SOURCE_UNMAPPED (not FAILED): sum_diff, sum_seq_gt0P, sum_pred_diff."
echo "Logs: $log_dir"
