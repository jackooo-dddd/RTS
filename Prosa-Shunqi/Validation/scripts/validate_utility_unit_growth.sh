#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/unit_growth"
cluster_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/cluster_results"
publish_dir="$VALIDATION_ROOT/imported/utility_foundation"
common_src_dir="$VALIDATION_ROOT/certificates/common"
certificate_src_dir="$VALIDATION_ROOT/certificates/utility_foundation"
fixture_dir="$VALIDATION_ROOT/fixtures/utility_foundation"
pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
mkdir -p "$log_dir" "$cluster_dir" "$publish_dir" "$pipeline_dir"

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" \
  --output "$log_dir/baseline_before.json" \
  > "$log_dir/baseline_before.log"

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/UnitGrowth.lean"; then
  echo "forbidden production proof escape in Prosa/Util/UnitGrowth.lean" >&2
  exit 1
fi
for path in \
  "$common_src_dir/LogicalRelation.v" \
  "$common_src_dir/SubadditivityNatCorrespondence.v" \
  "$common_src_dir/NatSubCorrespondence.v" \
  "$common_src_dir/UnitGrowthCorrespondence.v" \
  "$certificate_src_dir/UnitGrowthCertificate.v" \
  "$certificate_src_dir/UnitGrowthAssumptionAudit.v"; do
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
if rg -n '\b(Admitted|admit)\b|\bsorry\b' "$common_src_dir/PropSPropFoundation.v"; then
  echo "forbidden proof escape in Prop/SProp foundation" >&2
  exit 1
fi

work=$(validation_fresh_workdir utility_unit_growth)
mkdir -p "$work/olean/Prosa/Util" "$work/source/util" \
  "$work/imported" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

# Rebuild the complete production dependency path in a new output tree.
validation_compile_lean_module "$work" "Prosa/Util/Rel" \
  > "$log_dir/fresh_Rel.log" 2>&1
validation_compile_lean_module "$work" "Prosa/Util/UnitGrowth" \
  > "$log_dir/fresh_UnitGrowth.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanUnitGrowthAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/unit_growth_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

statement_only=$'Prosa.Util.UnitGrowth.unit_growth_function_k_steps_bounded\nProsa.Util.UnitGrowth.exists_intermediate_point\nProsa.Util.UnitGrowth.exists_intermediate_point_leq\nProsa.Util.UnitGrowth.exists_first_intermediate_point\nProsa.Util.UnitGrowth.slowed_respects_pointwise_leq\nProsa.Util.UnitGrowth.slowed_is_unit_step\nProsa.Util.UnitGrowth.slowed_respects_monotone\nProsa.Util.UnitGrowth.slowed_never_exceeds\nProsa.Util.UnitGrowth.bound_preserved_under_slowed\nProsa.Util.UnitGrowth.slowed_subtraction_value_preservation'
body_theorems=$'Prosa.Util.UnitGrowth.slowed.eq_1\nProsa.Util.UnitGrowth.slowed.eq_2'
export LEAN4EXPORT_STATEMENT_ONLY="$statement_only"
export LEAN4EXPORT_BODY_THEOREMS="$body_theorems"
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" "Prosa.Util.UnitGrowth" -- \
  Prosa.Util.UnitGrowth.unit_growth_function \
  Prosa.Util.UnitGrowth.unit_growth_function_k_steps_bounded \
  Prosa.Util.UnitGrowth.exists_intermediate_point \
  Prosa.Util.UnitGrowth.exists_intermediate_point_leq \
  Prosa.Util.UnitGrowth.exists_first_intermediate_point \
  Prosa.Util.UnitGrowth.slowed \
  Prosa.Util.UnitGrowth.slowed.eq_1 \
  Prosa.Util.UnitGrowth.slowed.eq_2 \
  Prosa.Util.UnitGrowth.slowed_respects_pointwise_leq \
  Prosa.Util.UnitGrowth.slowed_is_unit_step \
  Prosa.Util.UnitGrowth.slowed_respects_monotone \
  Prosa.Util.UnitGrowth.slowed_never_exceeds \
  Prosa.Util.UnitGrowth.bound_preserved_under_slowed \
  Prosa.Util.UnitGrowth.slowed_subtraction_value_preservation \
  > "$work/imported/UnitGrowth.out" 2> "$log_dir/export_UnitGrowth.log"

# The unchanged official file currently overflows Rocq 9.3's stack in legacy
# proof automation. Acquire the two computational bodies byte-for-byte and
# all theorem statements from the already verified post-Section Check types.
cp "$SOURCE_ROOT/util/tactics.v" "$work/source/util/tactics.v"
cp "$SOURCE_ROOT/util/notation.v" "$work/source/util/notation.v"
cp "$SOURCE_ROOT/util/rel.v" "$work/source/util/rel.v"
[[ $(validation_sha256 "$SOURCE_ROOT/util/unit_growth.v") == \
   c74cc6169150abdf2401953588c36f5744bf780def785ab084f8c3299e8d178b ]]
(cd "$work/source" && patch -p1 --forward --batch < \
  "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch") \
  > "$log_dir/source_patch_tactics.log" 2>&1
for source in tactics notation rel; do
  (cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
    rocq c -R "$work/source" prosa "util/$source.v") \
    > "$log_dir/official_${source}_compile.log" 2>&1
done
declarations=unit_growth_function,unit_growth_function_k_steps_bounded,exists_intermediate_point,exists_intermediate_point_leq,exists_first_intermediate_point,slowed,slowed_respects_pointwise_leq,slowed_is_unit_step,slowed_respects_monotone,slowed_never_exceeds,bound_preserved_under_slowed,slowed_subtraction_value_preservation
python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" \
  --source-file util/unit_growth.v \
  --module GeneratedUnitGrowthSource \
  --declarations "$declarations" \
  --computational unit_growth_function,slowed \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.unit_growth \
  --output "$work/source/GeneratedUnitGrowthSource.v" \
  --metadata "$work/source/unit_growth_source_extraction.json" \
  > "$log_dir/source_extraction.log"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedUnitGrowthSource.v) \
  > "$log_dir/generated_source_compile.log" 2>&1
cp "$work/source/unit_growth_source_extraction.json" \
  "$log_dir/source_extraction.json"

cp "$publish_dir/ImportedUnitGrowth.v" "$work/imported/ImportedUnitGrowth.v"
accepted_nat="$publish_dir/ImportedNat.vo"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_nat") == \
   322b510258fcbc7ab3f0e006548e913293839d5b13b3ee6698c546a9f9fe34d6 ]]
[[ $(validation_sha256 "$accepted_subadd") == \
   99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_nat" "$work/imported/"
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedUnitGrowth.v) \
  > "$log_dir/import_UnitGrowth.log" 2>&1

cp "$common_src_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence,NatSubCorrespondence,UnitGrowthCorrespondence}.v \
  "$work/certificates/"
cp "$certificate_src_dir/"{UnitGrowthCertificate,UnitGrowthAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  NatSubCorrespondence UnitGrowthCorrespondence UnitGrowthCertificate \
  UnitGrowthAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_UnitGrowthAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$certificate_src_dir/unit_growth_assumption_config.json" \
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
  --config "$certificate_src_dir/unit_growth_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/unit_growth.json" \
  > "$log_dir/publication.log"

# Publish canonical artifacts only after every gate above succeeds.
cp "$work/imported/UnitGrowth.out" "$publish_dir/UnitGrowth.out"
cp "$work/imported/ImportedUnitGrowth.vo" "$publish_dir/ImportedUnitGrowth.vo"
for module in UnitGrowthCorrespondence UnitGrowthCertificate UnitGrowthAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 "$script_dir/generate_utility_foundation_results.py" \
  > "$log_dir/aggregate_status.log"

(cd "$REPO_ROOT" && git diff --check)

echo "util/unit_growth.v = ACCEPTED_V06_FILE"
echo "accepted declarations: 12 / 12"
echo "fresh work directory: $work"
