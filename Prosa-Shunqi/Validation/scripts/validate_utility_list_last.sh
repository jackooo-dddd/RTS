#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/list_last"
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

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/List.lean"; then
  echo "forbidden production proof escape in Prosa/Util/List.lean" >&2
  exit 1
fi
for path in \
  "$common_src_dir/LogicalRelation.v" \
  "$common_src_dir/SubadditivityNatCorrespondence.v" \
  "$certificate_src_dir/ListLastCertificate.v" \
  "$certificate_src_dir/ListRemCertificate.v" \
  "$certificate_src_dir/ListLastTypeAudit.v" \
  "$certificate_src_dir/ListLastAssumptionAudit.v"; do
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

work=$(validation_fresh_workdir utility_list_last)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/utility_foundation" \
  "$work/source/util" "$work/imported" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

# Fresh isolated production build and proof/freeze audit.
validation_compile_lean_module "$work" "Prosa/Util/Tactics" \
  > "$log_dir/fresh_Tactics.log" 2>&1
validation_compile_lean_module "$work" "Prosa/Util/Supremum" \
  > "$log_dir/fresh_Supremum.log" 2>&1
validation_compile_lean_module "$work" "Prosa/Util/List" \
  > "$log_dir/fresh_List.log" 2>&1
validation_compile_lean_module "$work" \
  "Validation/fixtures/utility_foundation/ListLastComputationInterface" \
  > "$log_dir/fresh_computation_interface.log" 2>&1
{
  lean -DautoImplicit=false "$fixture_dir/LeanListLastAudit.lean"
  lean -DautoImplicit=false "$fixture_dir/LeanListMaxAudit.lean"
  lean -DautoImplicit=false "$fixture_dir/LeanListRemAudit.lean"
} > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/list_last_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

# Exact theorem types are statement-only.  The small monomorphic computation
# interface is exported with bodies; every such Lean proof is `rfl`.
export LEAN4EXPORT_STATEMENT_ONLY=$'Prosa.Util.List.last0_cons\nProsa.Util.List.last0_cat\nProsa.Util.List.last0_nth\nProsa.Util.List.last0_ex_cat\nProsa.Util.List.last0_filter\nProsa.Util.List.max0_cons\nProsa.Util.List.max0_of_uniform_set\nProsa.Util.List.in_max0_le\nProsa.Util.List.max0_in_seq\nProsa.Util.List.max0_2cons_eq\nProsa.Util.List.max0_2cons_le\nProsa.Util.List.max0_rem0\nProsa.Util.List.last_of_seq_le_max_of_seq\nProsa.Util.List.max_of_dominating_seq\nProsa.Util.List.nth0_cons\nProsa.Util.List.rem_in\nProsa.Util.List.in_neq_impl_rem_in\nProsa.Util.List.filter_size_rem\nProsa.Util.List.in_seq_equiv_undup\nProsa.Util.List.seq1_some\nProsa.Util.List.seq_elim_last\nProsa.Util.List.in_cat'
export LEAN4EXPORT_BODY_THEOREMS=$'Prosa.Validation.ListLastInterface.nat_zero\nProsa.Validation.ListLastInterface.nat_one\nProsa.Validation.ListLastInterface.append_nil\nProsa.Validation.ListLastInterface.append_cons\nProsa.Validation.ListLastInterface.filter_nil\nProsa.Validation.ListLastInterface.filter_cons\nProsa.Validation.ListLastInterface.length_nil\nProsa.Validation.ListLastInterface.length_cons\nProsa.Validation.ListLastInterface.length_cons_succ\nProsa.Validation.ListLastInterface.getD_nil\nProsa.Validation.ListLastInterface.getD_zero\nProsa.Validation.ListLastInterface.getD_succ\nProsa.Validation.ListLastInterface.getD_succ_direct\nProsa.Validation.ListLastInterface.sub_zero\nProsa.Validation.ListLastInterface.sub_succ\nProsa.Validation.ListLastInterface.sub_one\nProsa.Validation.ListLastInterface.generic_erase_nil\nProsa.Validation.ListLastInterface.generic_erase_cons\nProsa.Validation.ListLastInterface.generic_filter_nil\nProsa.Validation.ListLastInterface.generic_filter_cons\nProsa.Validation.ListLastInterface.generic_length_nil\nProsa.Validation.ListLastInterface.generic_length_cons\nProsa.Validation.ListLastInterface.generic_mem_eraseDups'
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" \
  "Validation.fixtures.utility_foundation.ListLastComputationInterface" -- \
  Prosa.Util.List.last0_cons \
  Prosa.Util.List.last0_cat \
  Prosa.Util.List.last0_nth \
  Prosa.Util.List.last0_ex_cat \
  Prosa.Util.List.last0_filter \
  Prosa.Util.List.max0_cons \
  Prosa.Util.List.max0_of_uniform_set \
  Prosa.Util.List.in_max0_le \
  Prosa.Util.List.max0_in_seq \
  Prosa.Util.List.max0_2cons_eq \
  Prosa.Util.List.max0_2cons_le \
  Prosa.Util.List.max0_rem0 \
  Prosa.Util.List.last_of_seq_le_max_of_seq \
  Prosa.Util.List.max_of_dominating_seq \
  Prosa.Util.List.nth0_cons \
  Prosa.Util.List.rem_in \
  Prosa.Util.List.in_neq_impl_rem_in \
  Prosa.Util.List.filter_size_rem \
  Prosa.Util.List.in_seq_equiv_undup \
  Prosa.Util.List.seq1_some \
  Prosa.Util.List.seq_elim_last \
  Prosa.Util.List.in_cat \
  Prosa.Validation.ListLastInterface.nat_zero \
  Prosa.Validation.ListLastInterface.nat_one \
  Prosa.Validation.ListLastInterface.append_nil \
  Prosa.Validation.ListLastInterface.append_cons \
  Prosa.Validation.ListLastInterface.filter_nil \
  Prosa.Validation.ListLastInterface.filter_cons \
  Prosa.Validation.ListLastInterface.length_nil \
  Prosa.Validation.ListLastInterface.length_cons \
  Prosa.Validation.ListLastInterface.length_cons_succ \
  Prosa.Validation.ListLastInterface.getD_nil \
  Prosa.Validation.ListLastInterface.getD_zero \
  Prosa.Validation.ListLastInterface.getD_succ \
  Prosa.Validation.ListLastInterface.getD_succ_direct \
  Prosa.Validation.ListLastInterface.sub_zero \
  Prosa.Validation.ListLastInterface.sub_succ \
  Prosa.Validation.ListLastInterface.sub_one \
  Prosa.Validation.ListLastInterface.generic_erase_nil \
  Prosa.Validation.ListLastInterface.generic_erase_cons \
  Prosa.Validation.ListLastInterface.generic_filter_nil \
  Prosa.Validation.ListLastInterface.generic_filter_cons \
  Prosa.Validation.ListLastInterface.generic_length_nil \
  Prosa.Validation.ListLastInterface.generic_length_cons \
  Prosa.Validation.ListLastInterface.generic_mem_eraseDups \
  > "$work/imported/ListLast.out" 2> "$log_dir/export.log"
[[ -s "$work/imported/ListLast.out" ]]

# Automatically acquire the exact official v0.6 definition dependency and
# elaborated theorem statements; no source theorem proof body is copied.
cp "$SOURCE_ROOT/util/tactics.v" "$work/source/util/tactics.v"
cp "$SOURCE_ROOT/util/supremum.v" "$work/source/util/supremum.v"
(cd "$work/source" && patch -p1 --forward --batch < \
  "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch") \
  > "$log_dir/source_patch_tactics.log" 2>&1
for source in tactics supremum; do
  (cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
    rocq c -R "$work/source" prosa "util/$source.v") \
    > "$log_dir/source_${source}_compile.log" 2>&1
done
python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" \
  --source-file util/list.v \
  --module GeneratedListLastSource \
  --declarations last0,max0,last0_cons,last0_cat,last0_nth,last0_ex_cat,last0_filter,max0_cons,max0_of_uniform_set,in_max0_le,max0_in_seq,max0_2cons_eq,max0_2cons_le,max0_rem0,last_of_seq_le_max_of_seq,max_of_dominating_seq,nth0_cons,rem_in,in_neq_impl_rem_in,filter_size_rem,in_seq_equiv_undup,seq1_some,seq_elim_last,in_cat \
  --computational last0,max0 \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.list \
  --output "$work/source/GeneratedListLastSource.v" \
  --metadata "$work/source/list_last_source_extraction.json" \
  > "$log_dir/source_extraction.log"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedListLastSource.v) \
  > "$log_dir/generated_source_compile.log" 2>&1
cp "$work/source/list_last_source_extraction.json" \
  "$log_dir/source_extraction.json"

cp "$fixture_dir/ImportedListLast.v" "$work/imported/ImportedListLast.v"
cp "$fixture_dir/ImportedListLastTypeProbe.v" \
  "$work/imported/ImportedListLastTypeProbe.v"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
   99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedListLast.v) \
  > "$log_dir/import.log" 2>&1
(cd "$work/imported" && validation_rocq_compile "$work" \
  ImportedListLastTypeProbe.v) \
  > "$log_dir/imported_interface.log" 2>&1

cp "$common_src_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence}.v \
  "$work/certificates/"
cp "$certificate_src_dir/"{ListLastCertificate,ListRemCertificate,ListLastTypeAudit,ListLastAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  ListLastCertificate ListRemCertificate ListLastTypeAudit ListLastAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_ListLastAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$certificate_src_dir/list_last_assumption_config.json" \
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
  --config "$certificate_src_dir/list_last_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/list_last.json" \
  > "$log_dir/publication.log"

cp "$work/imported/ListLast.out" "$publish_dir/ListLast.out"
cp "$work/imported/ImportedListLast.v" "$publish_dir/ImportedListLast.v"
cp "$work/imported/ImportedListLast.vo" "$publish_dir/ImportedListLast.vo"
for module in ListLastCertificate ListRemCertificate ListLastTypeAudit ListLastAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 "$script_dir/generate_utility_foundation_results.py" \
  > "$log_dir/aggregate_status.log"
# Rocq's pretty-printer can emit harmless line-end spaces in machine logs;
# normalize those logs before the repository-wide whitespace integrity gate.
perl -pi -e 's/[ \t]+$//' "$log_dir"/*.log
(cd "$REPO_ROOT" && git diff --check)

echo "util/list.v last0/max0/nth/rem theorem cluster: 22 / 22 ACCEPTED"
echo "util/list.v cumulative: 25 / 57 ACCEPTED"
echo "fresh work directory: $work"
