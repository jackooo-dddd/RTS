#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/list"
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

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/List.lean"; then
  echo "forbidden production proof escape in Prosa/Util/List.lean" >&2
  exit 1
fi
for path in \
  "$common_src_dir/LogicalRelation.v" \
  "$common_src_dir/SubadditivityNatCorrespondence.v" \
  "$certificate_src_dir/ListSimpleCertificate.v" \
  "$certificate_src_dir/ListSimpleAssumptionAudit.v"; do
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

work=$(validation_fresh_workdir utility_list_simple)
mkdir -p "$work/olean/Prosa/Util" "$work/source/util" \
  "$work/imported" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

# Build the production dependency path from source into an isolated output tree.
validation_compile_lean_module "$work" "Prosa/Util/Tactics" \
  > "$log_dir/fresh_Tactics.log" 2>&1
validation_compile_lean_module "$work" "Prosa/Util/Supremum" \
  > "$log_dir/fresh_Supremum.log" 2>&1
validation_compile_lean_module "$work" "Prosa/Util/List" \
  > "$log_dir/fresh_List.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanListSimpleAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/list_simple_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

# Export only the actual three compiled definition bodies in this cluster.
export LEAN4EXPORT_STATEMENT_ONLY=
export LEAN4EXPORT_BODY_THEOREMS=
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" "Prosa.Util.List" -- \
  Prosa.Util.List.max0 \
  Prosa.Util.List.first0 \
  Prosa.Util.List.last0 \
  > "$work/imported/ListSimple.out" 2> "$log_dir/export.log"

# Compile the exact required official-source context, with the existing
# syntax-only Rocq 9.3 tactics compatibility patch, then extract the three
# computational bodies automatically from pinned v0.6.
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
  --module GeneratedListSimpleSource \
  --declarations max0,first0,last0 \
  --computational max0,first0,last0 \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.list \
  --output "$work/source/GeneratedListSimpleSource.v" \
  --metadata "$work/source/list_simple_source_extraction.json" \
  > "$log_dir/source_extraction.log"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedListSimpleSource.v) \
  > "$log_dir/generated_source_compile.log" 2>&1
cp "$work/source/list_simple_source_extraction.json" \
  "$log_dir/source_extraction.json"

cp "$fixture_dir/ImportedListSimple.v" "$work/imported/ImportedListSimple.v"
cp "$fixture_dir/ImportedListSimpleTypeProbe.v" \
  "$work/imported/ImportedListSimpleTypeProbe.v"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
   99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedListSimple.v) \
  > "$log_dir/import.log" 2>&1
(cd "$work/imported" && validation_rocq_compile "$work" \
  ImportedListSimpleTypeProbe.v) \
  > "$log_dir/imported_interface.log" 2>&1

cp "$common_src_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence}.v \
  "$work/certificates/"
cp "$certificate_src_dir/"{ListSimpleCertificate,ListSimpleAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  ListSimpleCertificate ListSimpleAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_ListSimpleAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$certificate_src_dir/list_simple_assumption_config.json" \
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
  --config "$certificate_src_dir/list_simple_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/list_simple.json" \
  > "$log_dir/publication.log"

# Publish canonical evidence only after every gate succeeds.
cp "$work/imported/ListSimple.out" "$publish_dir/ListSimple.out"
cp "$work/imported/ImportedListSimple.v" "$publish_dir/ImportedListSimple.v"
cp "$work/imported/ImportedListSimple.vo" "$publish_dir/ImportedListSimple.vo"
for module in ListSimpleCertificate ListSimpleAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 "$script_dir/generate_utility_foundation_results.py" \
  > "$log_dir/aggregate_status.log"

(cd "$REPO_ROOT" && git diff --check)

echo "util/list.v starter cluster: 3 / 57 ACCEPTED"
echo "fresh work directory: $work"
