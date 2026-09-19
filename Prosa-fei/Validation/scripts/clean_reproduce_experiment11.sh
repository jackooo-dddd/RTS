#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
prosa_root=$(cd "$validation_root/.." && pwd)
repository_root=$(git -C "$prosa_root" rev-parse --show-toplevel)
repo_rel=${prosa_root#"$repository_root/"}
switch_name=${IMPORT_OPAM_SWITCH:-rocq93rc1}
importer_src=${ROCQLI_SRC:-/private/tmp/rocq-lean-import-93}
prosa_src=${PROSA_ROCQ_SRC:-/Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6}
outer_log="$validation_root/reports/logs/experiment11"
mkdir -p "$outer_log"

scratch=$(mktemp -d "${TMPDIR:-/tmp}/prosa-exp11-clean.XXXXXX")
scratch_repo="$scratch/TranslationProof"
scratch_prosa="$scratch_repo/$repo_rel"
mkdir -p "$scratch_repo"
rsync -a "$repository_root/.git" "$scratch_repo/"
mkdir -p "$(dirname "$scratch_prosa")"
rsync -a \
  --exclude='Validation/.work/' \
  --exclude='Validation/export/*.out' \
  --exclude='Validation/reports/logs/' \
  --exclude='*.olean' --exclude='*.vo' --exclude='*.glob' --exclude='.*.aux' \
  "$prosa_root/" "$scratch_prosa/"

v="$scratch_prosa/Validation"
logs="$v/reports/logs/experiment11_clean"
mkdir -p "$logs" "$v/export" "$v/.work"
echo "clean scratch repository: $scratch_repo" | tee "$logs/clean_root.log"
if find "$v" -type f \( -name '*.olean' -o -name '*.vo' -o -name '*.glob' -o -name '.*.aux' \) | grep -q .; then
  echo "clean copy contains forbidden compiled object" >&2
  exit 1
fi

checked=(
  "$v/rocq/PropSPropFoundation.v"
  "$v/rocq/FiniteNatSumBridge.v"
  "$v/rocq/FiniteNatSumReuseCertificates.v"
  "$v/rocq/JobArrivalCleanCertificate.v"
  "$v/rocq/CompletesAtSemanticCertificate.v"
  "$v/rocq/CompletesAtGenericCertificate.v"
  "$v/lean_tools/FiniteSumNormalizationGuards.lean"
  "$v/lean_fixtures/completes_at_corrected/CompletesAtCorrected.lean"
)
if rg -n '\b(Admitted|admit|sorry)\b' "${checked[@]}"; then
  echo "forbidden proof escape in clean reproduction inputs" >&2
  exit 1
fi
unexpected_axioms=$(rg -n '\bAxiom\b' "${checked[@]}" | \
  rg -v 'PropSPropFoundation\.v:.*interpret_strict' || true)
if [[ -n "$unexpected_axioms" ]]; then
  echo "$unexpected_axioms" >&2
  echo "unexpected axiom in clean reproduction inputs" >&2
  exit 1
fi

cd "$scratch_prosa"
sum_targets=big_nat_eq0,sum_of_ones,sum_le_summation_range
python3 Validation/scripts/extract_rocq_declarations.py \
  --mapping Validation/mapping/hard_validation_targets.yaml \
  --source-root "$prosa_src" --target-keys "$sum_targets" \
  --output-dir Validation/.work/source_snapshots \
  --metadata "$logs/sum_source_fidelity.json"
python3 Validation/scripts/extract_rocq_declarations.py \
  --mapping Validation/mapping/rts_validation_targets.yaml \
  --source-root "$prosa_src" \
  --target-keys completes_at_current,completes_at_corrected \
  --output-dir Validation/.work/source_snapshots \
  --metadata "$logs/completes_source_fidelity.json"
python3 Validation/scripts/generate_rocq_source_modules.py \
  --mapping Validation/mapping/hard_validation_targets.yaml \
  --source-root "$prosa_src" --output-dir Validation/rocq/generated_hard

HARD_LOG_PREFIX=experiment11_clean/finite_sum \
HARD_ALL_THEOREMS_STATEMENT_ONLY=1 HARD_TARGET_KEYS="$sum_targets" \
HARD_ARTIFACT="$v/export/FiniteNatSumNormalizedTargets.out" \
  Validation/scripts/export_hard_validation.sh > "$logs/finite_sum_export_run.log" 2>&1
HARD_LOG_PREFIX=experiment11_clean/finite_sum_definition_graph \
HARD_ALL_THEOREMS_STATEMENT_ONLY=1 HARD_TARGET_KEYS="$sum_targets" \
HARD_NORMALIZE_THEOREM_TYPES= HARD_NORMALIZE_SUBEXPRESSION_HEADS= \
HARD_ARTIFACT="$v/export/FiniteNatSumTargets.out" \
  Validation/scripts/export_hard_validation.sh > "$logs/finite_sum_definition_graph_export_run.log" 2>&1
COMPLETES_LOG_EXPERIMENT=experiment11_clean \
  Validation/scripts/export_completes_at_validation.sh > "$logs/completes_export_run.log" 2>&1
JOB_ARRIVAL_LOG_EXPERIMENT=experiment11_clean \
  Validation/scripts/export_job_arrival_minimal.sh > "$logs/job_arrival_export_run.log" 2>&1

build=$(awk -F': ' '/Fresh build directory:/ {print $2}' \
  "$logs/finite_sum_lean_export_manifest.log")
mathlib_path=$(cd /private/tmp/mathlib4-v4.33.1 && lake env printenv LEAN_PATH)
export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
export LEAN_PATH="$build:$scratch_prosa:$mathlib_path"
mkdir -p "$build/Validation/lean_tools"
lean -R "$scratch_prosa" \
  -o "$build/Validation/lean_tools/FiniteSumNormalizationGuards.olean" \
  Validation/lean_tools/FiniteSumNormalizationGuards.lean \
  > "$logs/normalization_guards.log" 2>&1
set +e
lean -R "$scratch_prosa" Validation/lean_tools/FiniteSumNormalizationBadIdentity.lean \
  > "$logs/normalization_bad_identity.log" 2>&1
bad_rc=$?
set -e
[[ $bad_rc -ne 0 ]] && rg -q EXPECTED_REJECTION "$logs/normalization_bad_identity.log"

compile() {
  local file=$1 log=$2
  opam exec --switch="$switch_name" -- rocq c \
    -R "$prosa_src" prosa \
    -Q "$importer_src/src" LeanImport -I "$importer_src/src" \
    -Q generated_hard HardSource "$file" > "$logs/$log" 2>&1
}

cd "$v/rocq"
ulimit -s 65520
compile PropSPropFoundation.v foundation.log
compile generated_hard/Generated_util__sum.v official_sum.log
compile CompletesAtSourceFidelity.v completes_source_type.log
compile ImportedFiniteNatSumNormalized93.v imported_sum.log
compile ImportedBigNatEq093.v imported_sum_definition_graph.log
compile HardSumCertificate.v hard_sum.log
compile FiniteNatSumBridge.v sum_bridge.log
compile FiniteNatSumReuseCertificates.v sum_certificates.log
compile ImportedJobArrivalClean93.v imported_job_arrival.log
compile JobArrivalCleanCertificate.v job_arrival_certificate.log
compile ImportedCompletesAt93.v imported_completes.log
compile CompletesAtSemanticCertificate.v completes_concrete.log
compile CompletesAtGenericCertificate.v completes_generic.log
compile AssumptionAuditExperiment11Clean.v clean_assumptions.log

cd "$v"
python3 scripts/classify_assumptions.py \
  --config mapping/experiment11_clean_assumption_audit.yaml \
  --log "$logs/clean_assumptions.log" \
  --output "$logs/clean_assumption_summary.json" \
  > "$logs/clean_assumption_classification.log"

python3 scripts/artifact_provenance.py record \
  --manifest "$logs/clean_artifact_provenance.json" \
  --source "$scratch_prosa/Prosa/Util/Sum.lean" \
  --source "$scratch_prosa/Prosa/Behavior/Job.lean" \
  --source "$v/lean_fixtures/completes_at_corrected/CompletesAtCorrected.lean" \
  --artifact "$v/export/FiniteNatSumNormalizedTargets.out" \
  --artifact "$v/export/FiniteNatSumTargets.out" \
  --artifact "$v/export/JobArrivalMinimal.out" \
  --artifact "$v/export/CompletesAtValidation.out" \
  --imported "$v/rocq/ImportedFiniteNatSumNormalized93.vo" \
  --imported "$v/rocq/ImportedBigNatEq093.vo" \
  --imported "$v/rocq/ImportedJobArrivalClean93.vo" \
  --imported "$v/rocq/ImportedCompletesAt93.vo" > "$logs/provenance_record.log"
python3 scripts/artifact_provenance.py verify \
  --manifest "$logs/clean_artifact_provenance.json" \
  --source "$scratch_prosa/Prosa/Util/Sum.lean" \
  --source "$scratch_prosa/Prosa/Behavior/Job.lean" \
  --source "$v/lean_fixtures/completes_at_corrected/CompletesAtCorrected.lean" \
  --artifact "$v/export/FiniteNatSumNormalizedTargets.out" \
  --artifact "$v/export/FiniteNatSumTargets.out" \
  --artifact "$v/export/JobArrivalMinimal.out" \
  --artifact "$v/export/CompletesAtValidation.out" \
  --imported "$v/rocq/ImportedFiniteNatSumNormalized93.vo" \
  --imported "$v/rocq/ImportedBigNatEq093.vo" \
  --imported "$v/rocq/ImportedJobArrivalClean93.vo" \
  --imported "$v/rocq/ImportedCompletesAt93.vo" > "$logs/provenance_verify.log"

python3 - "$logs/clean_assumption_summary.json" <<'PY' > "$logs/clean_summary.txt"
import json, sys
d = json.load(open(sys.argv[1]))["certificates"]
for key in ["big_nat_eq0", "sum_le_summation_range", "job_arrival",
            "completes_at_counterexample", "completes_at_corrected",
            "completes_at_generic"]:
    print(f"{key:32} {d[key]['status']}")
PY

rsync -a "$logs/" "$outer_log/clean_reproduction/"
{
  echo "clean scratch repository: $scratch_repo"
  cat "$logs/clean_summary.txt"
  shasum -a 256 "$v/export/FiniteNatSumNormalizedTargets.out"
  shasum -a 256 "$v/export/JobArrivalMinimal.out"
  shasum -a 256 "$v/export/CompletesAtValidation.out"
  cat "$logs/provenance_verify.log"
  echo "wrong normalization guard: REJECTED"
} | tee "$outer_log/clean_reproduction_summary.log"
