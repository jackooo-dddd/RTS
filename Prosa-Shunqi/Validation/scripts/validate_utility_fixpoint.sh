#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/translation_order/fixpoint"
fixture_dir="$VALIDATION_ROOT/fixtures/translation_order"
common_dir="$VALIDATION_ROOT/certificates/common"
cert_dir="$VALIDATION_ROOT/certificates/utility_foundation"
config="$VALIDATION_ROOT/tooling/util_fixpoint_export_config.json"
mkdir -p "$log_dir"

[[ $(validation_sha256 "$SOURCE_ROOT/util/fixpoint.v") == \
  46a522e8375148c5bd916915bd0428e44409429670013a727f189603ec1facdf ]]
[[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/fixpoint.v" for r in csv.DictReader(open(sys.argv[1]))))' \
  "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 17 ]]
if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Fixpoint.lean"; then
  echo 'forbidden production proof escape' >&2; exit 1
fi
for module in FixpointBaseCorrespondence FixpointMonotoneCorrespondence \
  FixpointTheoremCorrespondence FixpointMaxOperations \
  FixpointMaxTheoremCorrespondence; do
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$common_dir/$module.v"; then
    echo "forbidden certificate proof escape in $module" >&2; exit 1
  fi
done

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_before.json" \
  > "$log_dir/baseline_before.log"

work=$(validation_fresh_workdir translation_order_fixpoint)
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/translation_order" \
  "$work/imported" "$work/official/util" "$work/source" "$work/certificates"
validation_prepare_lean_path "$work"
export VALIDATION_MODULE_TIMING_FILE="$log_dir/module_build_timing.jsonl"

for module in Tactics Nat Notation Rel Supremum List Setoid Minmax Fixpoint; do
  validation_compile_lean_module "$work" "Prosa/Util/$module" \
    > "$log_dir/fresh_${module}.log" 2>&1
done
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/translation_order/FixpointComputationInterface.olean" \
  "$fixture_dir/FixpointComputationInterface.lean" \
  > "$log_dir/fresh_interface.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanFixpointAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/fixpoint_lean_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

targets=()
while IFS= read -r target; do
  targets+=("$target")
done < <(jq -r '.targets[]' "$config")
export LEAN4EXPORT_STATEMENT_ONLY=$(jq -r '.statement_only | join("\n")' "$config")
export LEAN4EXPORT_BODY_THEOREMS=$(jq -r '.body_theorems | join("\n")' "$config")
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$EXPORTER_ROOT/.lake/build/bin/lean4export" \
  Validation.fixtures.translation_order.FixpointComputationInterface -- \
  "${targets[@]}" > "$work/imported/Fixpoint.out" 2> "$log_dir/export.log"
[[ -s "$work/imported/Fixpoint.out" ]]

cp "$SOURCE_ROOT/util/rel.v" "$work/official/util/rel.v"
(cd "$work/official" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -Q "$work/official" prosa util/rel.v) \
  > "$log_dir/source_rel_compile.log" 2>&1
declarations=$(jq -r '.targets[] | select(startswith("Prosa.Util.Fixpoint.")) | split(".")[-1]' "$config" | paste -sd, -)
for spec in 'GeneratedFixpointSource:find_fixpoint_from,find_fixpoint' \
  "GeneratedFixpointSourceAll:$declarations"; do
  module=${spec%%:*}
  names=${spec#*:}
  python3 "$script_dir/extract_v06_semantic_source.py" \
    --source-root "$SOURCE_ROOT" --source-file util/fixpoint.v \
    --module "$module" --declarations "$names" \
    --computational find_fixpoint_from,find_fixpoint,find_max_fixpoint_of_seq,find_max_fixpoint \
    --elaborated-evidence "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
    --qualified-prefix prosa.util.fixpoint \
    --drop-import 'Require Export prosa.util.list.' \
    --drop-import 'Require Export prosa.util.minmax.' \
    --output "$work/source/$module.v" \
    --metadata "$work/source/${module}_extraction.json" \
    > "$log_dir/source_${module}_extraction.log"
  (cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
    rocq c -Q "$work/official" prosa -Q "$work/source" '' "$module.v") \
    > "$log_dir/source_${module}_compile.log" 2>&1
done

[[ $(validation_sha256 "$VALIDATION_ROOT/imported/utility_foundation/Nat.out") == \
  eba900fd5d40c82f36fc2cc50b37a382c8d6f638e0050dfd5bc66cfc29888ecb ]]
[[ $(validation_sha256 "$VALIDATION_ROOT/imported/foundation_slice_2_closure/Subadditivity.out") == \
  9ca38bbffc3c1b052bb60aa3a2a091fd15aeb531f195124c604f970ca8243b50 ]]
cp "$VALIDATION_ROOT/imported/utility_foundation/"{Nat.out,ImportedNat.v} "$work/imported/"
cp "$VALIDATION_ROOT/imported/foundation_slice_2_closure/Subadditivity.out" "$work/imported/"
cp "$VALIDATION_ROOT/imported/foundation_slice_2/ImportedSubadditivity.v" "$work/imported/"
cp "$fixture_dir/ImportedFixpoint.v" "$work/imported/"
ulimit -s 65520
for module in ImportedSubadditivity ImportedNat ImportedFixpoint; do
  (cd "$work/imported" && opam exec --switch="$ROCQ_SWITCH" -- \
    rocq c -Q "$IMPORTER_ROOT/src" LeanImport -I "$IMPORTER_ROOT/src" \
      -Q "$work/imported" FoundationImported "$module.v") \
    > "$log_dir/import_${module}.log" 2>&1
done

for module in PropSPropFoundation LogicalRelation \
  SubadditivityNatCorrespondence NatSubCorrespondence \
  FixpointBaseCorrespondence FixpointMonotoneCorrespondence \
  FixpointTheoremCorrespondence FixpointMaxOperations \
  FixpointMaxTheoremCorrespondence; do
  cp "$common_dir/$module.v" "$work/certificates/"
done
cp "$cert_dir/FixpointAssumptionAudit.v" "$work/certificates/"
for module in PropSPropFoundation LogicalRelation \
  SubadditivityNatCorrespondence NatSubCorrespondence \
  FixpointBaseCorrespondence FixpointMonotoneCorrespondence \
  FixpointTheoremCorrespondence FixpointMaxOperations \
  FixpointMaxTheoremCorrespondence FixpointAssumptionAudit; do
  (cd "$work/certificates" && opam exec --switch="$ROCQ_SWITCH" -- rocq c \
    -Q "$IMPORTER_ROOT/src" LeanImport -I "$IMPORTER_ROOT/src" \
    -Q "$work/imported" FoundationImported \
    -Q "$work/official" prosa -Q "$work/source" '' \
    -Q "$work/certificates" FoundationCertificates "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
python3 "$script_dir/audit_assumptions.py" \
  --config "$cert_dir/fixpoint_assumption_config.json" \
  --log "$log_dir/rocq_FixpointAssumptionAudit.log" \
  --output "$log_dir/assumption_summary.json" \
  > "$log_dir/assumption_classifier.log"
jq -e '(.certificates | length) == 17 and
  ([.certificates[] | .status == "CERTIFIED" or
    .status == "CERTIFIED_WITH_PROP_SPROP_FOUNDATION"] | all) and
  ([.certificates[] | (.semantic_premises | length) == 0 and
    (.unexpected | length) == 0 and
    .source_theorem_dependency == false and
    .target_theorem_dependency == false and
    (.statement_only_dependencies | length) == 0] | all)' \
  "$log_dir/assumption_summary.json" > /dev/null
python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_after.json" \
  > "$log_dir/baseline_after.log"

echo "FIXPOINT_CERTIFICATES_17_OF_17_PASS"
python3 "$script_dir/file_validate_lean_dependencies.py" seal \
  --project "$PROJECT_ROOT" --olean "$work/olean" --mode CLEAN_FULL \
  --output "$work/lean_source_build_manifest.json"
snapshot=$(python3 "$script_dir/seal_utility_fixpoint_preparation.py" \
  --project "$PROJECT_ROOT" --work "$work")
cluster_dir="$VALIDATION_ROOT/logs/translation_order/cluster_results"
mkdir -p "$cluster_dir"
python3 "$script_dir/publish_utility_cluster.py" \
  --project-root "$PROJECT_ROOT" --validation-root "$VALIDATION_ROOT" \
  --source-root "$SOURCE_ROOT" --exporter-root "$EXPORTER_ROOT" \
  --importer-root "$IMPORTER_ROOT" --work "$work" \
  --config "$cert_dir/fixpoint_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --snapshot-id "$snapshot" \
  --prepare-manifest "$work/prepare_manifest.json" \
  --prepare-evidence "$work/prepare_run_evidence.json" \
  --output "$cluster_dir/fixpoint.json" \
  > "$log_dir/publication_cluster.log"
python3 "$script_dir/finalize_utility_fixpoint.py" \
  --project "$PROJECT_ROOT" --work "$work" \
  > "$log_dir/publication_status.log"
echo "fresh work directory: $work"
cat "$log_dir/publication_status.log"
