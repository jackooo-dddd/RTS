#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/search_arg"
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

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/SearchArg.lean"; then
  echo "forbidden production proof escape in Prosa/Util/SearchArg.lean" >&2
  exit 1
fi
for path in \
  "$common_src_dir/LogicalRelation.v" \
  "$common_src_dir/SubadditivityNatCorrespondence.v" \
  "$certificate_src_dir/SearchArgDefinitionCertificate.v" \
  "$certificate_src_dir/SearchArgStatementCertificate.v" \
  "$certificate_src_dir/SearchArgTypeAudit.v" \
  "$certificate_src_dir/SearchArgAssumptionAudit.v"; do
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

work=$(validation_fresh_workdir utility_search_arg)
mkdir -p "$work/olean/Prosa/Util" "$work/source/util" \
  "$work/imported" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

validation_compile_lean_module "$work" "Prosa/Util/Tactics" \
  > "$log_dir/fresh_Tactics.log" 2>&1
validation_compile_lean_module "$work" "Prosa/Util/SearchArg" \
  > "$log_dir/fresh_SearchArg.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanSearchArgAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/search_arg_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

statement_only=$'Prosa.Util.SearchArg.earliest_pred_element_exists_case\nProsa.Util.SearchArg.search_arg_none\nProsa.Util.SearchArg.search_arg_not_none\nProsa.Util.SearchArg.search_arg_pred\nProsa.Util.SearchArg.search_arg_in_range\nProsa.Util.SearchArg.search_arg_extremum\nProsa.Util.SearchArg.prop_on_ex_minn'
body_theorems=$'Prosa.Util.SearchArg.search_arg.eq_1\nProsa.Util.SearchArg.search_arg.eq_2'
export LEAN4EXPORT_STATEMENT_ONLY="$statement_only"
export LEAN4EXPORT_BODY_THEOREMS="$body_theorems"
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" "Prosa.Util.SearchArg" -- \
  Prosa.Util.SearchArg.earliest_pred_element_exists_case \
  Prosa.Util.SearchArg.search_arg \
  Prosa.Util.SearchArg.search_arg.eq_1 \
  Prosa.Util.SearchArg.search_arg.eq_2 \
  Prosa.Util.SearchArg.search_arg_none \
  Prosa.Util.SearchArg.search_arg_not_none \
  Prosa.Util.SearchArg.search_arg_pred \
  Prosa.Util.SearchArg.search_arg_in_range \
  Prosa.Util.SearchArg.search_arg_extremum \
  Prosa.Util.SearchArg.prop_on_ex_minn \
  > "$work/imported/SearchArg.out" 2> "$log_dir/export.log"

cp "$SOURCE_ROOT/util/tactics.v" "$work/source/util/tactics.v"
(cd "$work/source" && patch -p1 --forward --batch < \
  "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch") \
  > "$log_dir/source_patch_tactics.log" 2>&1
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa util/tactics.v) \
  > "$log_dir/official_tactics_compile.log" 2>&1

[[ $(validation_sha256 "$SOURCE_ROOT/util/search_arg.v") == \
  7bc98acacf5ff1a8d312f1bb6689046d2d21ce8d44b12f8a288f0ccb6106e122 ]]
declarations=earliest_pred_element_exists_case,search_arg,search_arg_none,search_arg_not_none,search_arg_pred,search_arg_in_range,search_arg_extremum,prop_on_ex_minn
python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" \
  --source-file util/search_arg.v \
  --module GeneratedSearchArgSource \
  --declarations "$declarations" \
  --computational search_arg \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.search_arg \
  --output "$work/source/GeneratedSearchArgSource.v" \
  --metadata "$work/source/search_arg_source_extraction.json" \
  > "$log_dir/source_extraction.log"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedSearchArgSource.v) \
  > "$log_dir/generated_source_compile.log" 2>&1
cp "$work/source/search_arg_source_extraction.json" \
  "$log_dir/source_extraction.json"

cp "$fixture_dir/ImportedSearchArg.v" "$work/imported/ImportedSearchArg.v"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
  99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedSearchArg.v) \
  > "$log_dir/import.log" 2>&1

cp "$common_src_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence}.v \
  "$work/certificates/"
cp "$certificate_src_dir/"{SearchArgDefinitionCertificate,SearchArgStatementCertificate,SearchArgTypeAudit,SearchArgAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  SearchArgDefinitionCertificate SearchArgStatementCertificate SearchArgTypeAudit \
  SearchArgAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_SearchArgAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$certificate_src_dir/search_arg_assumption_config.json" \
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
  --config "$certificate_src_dir/search_arg_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/search_arg.json" \
  > "$log_dir/publication.log"

cp "$work/imported/SearchArg.out" "$publish_dir/SearchArg.out"
cp "$work/imported/ImportedSearchArg.v" "$publish_dir/ImportedSearchArg.v"
cp "$work/imported/ImportedSearchArg.vo" "$publish_dir/ImportedSearchArg.vo"
for module in SearchArgDefinitionCertificate SearchArgStatementCertificate \
  SearchArgTypeAudit SearchArgAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 "$script_dir/generate_utility_foundation_results.py" \
  > "$log_dir/aggregate_status.log"

(cd "$REPO_ROOT" && git diff --check)

echo "util/search_arg.v = ACCEPTED_V06_FILE"
echo "accepted declarations: 8 / 8"
echo "fresh work directory: $work"
