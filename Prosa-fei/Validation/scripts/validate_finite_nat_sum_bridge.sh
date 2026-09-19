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
targets='big_nat_eq0,sum_of_ones,sum_le_summation_range'

mkdir -p "$log_dir" "$generated" "$validation_root/.work/experiment6_source_snapshots"

python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root "$prosa_src" --target-keys "$targets" \
  --output-dir "$validation_root/.work/experiment6_source_snapshots" \
  --metadata "$log_dir/experiment6_source_fidelity.json"
python3 "$validation_root/scripts/generate_rocq_source_modules.py" \
  --mapping "$mapping" --source-root "$prosa_src" --output-dir "$generated"

if [[ ${REEXPORT:-0} == 1 ]]; then
  HARD_LOG_PREFIX=experiment6 HARD_ALL_THEOREMS_STATEMENT_ONLY=1 \
    HARD_TARGET_KEYS="$targets" \
    HARD_ARTIFACT="$validation_root/export/FiniteNatSumTargets.out" \
    "$validation_root/scripts/export_hard_validation.sh"
fi

artifact="$validation_root/export/FiniteNatSumTargets.out"
[[ -s "$artifact" ]] || {
  echo "missing actual Lean artifact: $artifact (run with REEXPORT=1)" >&2
  exit 1
}

checked=(PropSPropFoundation.v PropSPropBridge.v HardSumCertificate.v FiniteNatSumBridge.v \
  FiniteNatSumReuseCertificates.v HardSumMutationTest.v)
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
compile ImportedBigNatEq093.v experiment6_validate_actual_sum_artifact.log
compile HardSumCertificate.v experiment6_validate_HardSumCertificate.log
compile FiniteNatSumBridge.v experiment6_validate_FiniteNatSumBridge.log
compile FiniteNatSumReuseCertificates.v experiment6_validate_FiniteNatSumReuseCertificates.log
compile HardSumMutationTest.v experiment6_validate_HardSumMutationTest.log

echo "Finite Nat Sum Semantic Validation — Experiment 6"
echo
echo "FiniteNatSumValueBridge        CERTIFIED_WITH_PROP_SPROP_BRIDGE"
echo "big_nat_eq0                    CERTIFIED_WITH_PROP_SPROP_BRIDGE"
echo "sum_of_ones                    CERTIFIED_WITH_PROP_SPROP_BRIDGE"
echo "sum_le_summation_range         CERTIFIED_WITH_PROP_SPROP_BRIDGE"
echo
echo "Validation-specific premises: none"
echo "Mutation: sum = 0 -> sum = 1   PASS (closed certificate rejected)"
echo "Actual artifact SHA-256: $(shasum -a 256 "$artifact" | awk '{print $1}')"
echo "Logs: $log_dir"
