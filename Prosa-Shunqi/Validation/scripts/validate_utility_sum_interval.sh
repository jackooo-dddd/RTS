#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/sum"
cluster_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/cluster_results"
publish_dir="$VALIDATION_ROOT/imported/utility_foundation"
common_src_dir="$VALIDATION_ROOT/certificates/common"
certificate_src_dir="$VALIDATION_ROOT/certificates/utility_foundation"
fixture_dir="$VALIDATION_ROOT/fixtures/utility_foundation"
mkdir -p "$log_dir" "$cluster_dir" "$publish_dir"

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" \
  --output "$log_dir/baseline_before.json" \
  > "$log_dir/baseline_before.log"

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Sum.lean"; then
  echo "forbidden production proof escape in Prosa/Util/Sum.lean" >&2
  exit 1
fi
for path in \
  "$common_src_dir/LogicalRelation.v" \
  "$common_src_dir/SubadditivityNatCorrespondence.v" \
  "$common_src_dir/SumIntervalCorrespondence.v" \
  "$certificate_src_dir/SumIntervalCertificate.v" \
  "$certificate_src_dir/SumIntervalTypeAudit.v" \
  "$certificate_src_dir/SumIntervalAssumptionAudit.v"; do
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
    echo "forbidden certificate proof escape in $path" >&2
    exit 1
  fi
done
foundation_axioms=$(rg -n '^Axiom ' "$common_src_dir/PropSPropFoundation.v" || true)
if [[ "$foundation_axioms" != *"Axiom interpret_strict"* ]] || \
   [[ $(printf '%s\n' "$foundation_axioms" | sed '/^$/d' | wc -l | tr -d ' ') != 1 ]]; then
  echo "Prop/SProp foundation axiom boundary changed" >&2
  exit 1
fi

work=$(validation_fresh_workdir utility_sum_interval)
mkdir -p "$work/olean/Prosa/Util" "$work/imported" \
  "$work/source/util" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

for module in Prosa/Util/Tactics Prosa/Util/Notation Prosa/Util/Rel \
  Prosa/Util/Nat Prosa/Util/Sum; do
  validation_compile_lean_module "$work" "$module" \
    > "$log_dir/fresh_${module##*/}.log" 2>&1
done
lean -DautoImplicit=false "$fixture_dir/LeanSumIntervalAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/sum_interval_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

# A Meta.isDefEq check plus an actual Eq.refl theorem declaration binds the
# normalization to this fresh compiled target.  The malformed fold identity
# must be rejected before any guard can be admitted.
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/FiniteSumNormalizationGuards.olean" \
  "$fixture_dir/FiniteSumNormalizationGuards.lean" \
  > "$log_dir/normalization_guards.log" 2>&1
[[ $(rg -c 'KERNEL_NORMALIZATION_GUARD .* proof=Eq.refl' \
  "$log_dir/normalization_guards.log") == 6 ]]
set +e
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  "$fixture_dir/FiniteSumNormalizationBadIdentity.lean" \
  > "$log_dir/normalization_negative.log" 2>&1
negative_rc=$?
set -e
if [[ $negative_rc -eq 0 ]] || \
   ! rg -q 'EXPECTED_REJECTION: bad fold identity is not definitionally equal' \
     "$log_dir/normalization_negative.log" || \
   rg -q 'BAD_NORMALIZATION_FALSE_POSITIVE|missing target theorem|don.t know how to synthesize' \
     "$log_dir/normalization_negative.log"; then
  echo "finite-sum normalization negative control failed" >&2
  exit 1
fi

theorems=$'Prosa.Util.Sum.sum_of_ones\nProsa.Util.Sum.big_nat_eq0\nProsa.Util.Sum.sum_le_summation_range\nProsa.Util.Sum.big_sum_eq_in_eq_sized_intervals\nProsa.Util.Sum.pigeonhole_on_interval\nProsa.Util.Sum.sum_ge_2_nat'
export LEAN4EXPORT_STATEMENT_ONLY="$theorems"
export LEAN4EXPORT_BODY_THEOREMS=
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES="$theorems"
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=Finset.sum
export LEAN4EXPORT_PRESERVE_REDUCIBLE_THEOREM_TYPES=1
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" "Prosa.Util.Sum" -- \
  Prosa.Util.Sum.sum_of_ones \
  Prosa.Util.Sum.big_nat_eq0 \
  Prosa.Util.Sum.sum_le_summation_range \
  Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals \
  Prosa.Util.Sum.pigeonhole_on_interval \
  Prosa.Util.Sum.sum_ge_2_nat \
  > "$work/imported/SumInterval.out" 2> "$log_dir/export.log"
[[ $(rg -c 'NORMALIZED_THEOREM_TYPE .* defeq=true' "$log_dir/export.log") == 6 ]]

cp "$SOURCE_ROOT/util/tactics.v" "$work/source/util/tactics.v"
cp "$SOURCE_ROOT/util/notation.v" "$work/source/util/notation.v"
cp "$SOURCE_ROOT/util/rel.v" "$work/source/util/rel.v"
cp "$SOURCE_ROOT/util/nat.v" "$work/source/util/nat.v"
(cd "$work/source" && patch -p1 --forward --batch < \
  "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch") \
  > "$log_dir/source_patch_tactics.log" 2>&1
for source in tactics notation rel nat; do
  (cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
    rocq c -R "$work/source" prosa "util/$source.v") \
    > "$log_dir/source_${source}_compile.log" 2>&1
done
python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" \
  --source-file util/sum.v \
  --module GeneratedSumIntervalSource \
  --declarations sum_of_ones,big_nat_eq0,sum_le_summation_range,big_sum_eq_in_eq_sized_intervals,pigeonhole_on_interval,sum_ge_2_nat \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.sum \
  --output "$work/source/GeneratedSumIntervalSource.v" \
  --metadata "$work/source/sum_interval_source_extraction.json" \
  > "$log_dir/source_extraction.log"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedSumIntervalSource.v) \
  > "$log_dir/generated_source_compile.log" 2>&1
cp "$work/source/sum_interval_source_extraction.json" \
  "$log_dir/source_extraction.json"

cp "$fixture_dir/ImportedSumInterval.v" "$work/imported/ImportedSumInterval.v"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
   99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedSumInterval.v) \
  > "$log_dir/import.log" 2>&1

cp "$common_src_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence,SumIntervalCorrespondence}.v \
  "$work/certificates/"
cp "$certificate_src_dir/"{SumIntervalCertificate,SumIntervalTypeAudit,SumIntervalAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  SumIntervalCorrespondence SumIntervalCertificate SumIntervalTypeAudit \
  SumIntervalAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_SumIntervalAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$certificate_src_dir/sum_interval_assumption_config.json" \
  --log "$log_dir/assumptions.log" \
  --output "$log_dir/assumption_summary.json" \
  > "$log_dir/assumption_classifier.log"

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" \
  --output "$log_dir/baseline_after.json" \
  > "$log_dir/baseline_after.log"

python3 "$script_dir/publish_utility_cluster.py" \
  --project-root "$PROJECT_ROOT" \
  --validation-root "$VALIDATION_ROOT" \
  --source-root "$SOURCE_ROOT" \
  --exporter-root "$EXPORTER_ROOT" \
  --importer-root "$IMPORTER_ROOT" \
  --work "$work" \
  --config "$certificate_src_dir/sum_interval_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/sum_interval.json" \
  > "$log_dir/publication.log"

cp "$work/imported/SumInterval.out" "$publish_dir/SumInterval.out"
cp "$work/imported/ImportedSumInterval.v" "$publish_dir/ImportedSumInterval.v"
cp "$work/imported/ImportedSumInterval.vo" "$publish_dir/ImportedSumInterval.vo"
for module in SumIntervalCorrespondence SumIntervalCertificate \
  SumIntervalTypeAudit SumIntervalAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 "$script_dir/generate_utility_foundation_results.py" \
  > "$log_dir/aggregate_status.log"

(cd "$REPO_ROOT" && git diff --check)

echo "util/sum.v interval cluster: 6 / 25 ACCEPTED"
echo "fresh work directory: $work"
