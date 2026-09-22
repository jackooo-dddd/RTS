#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/sum_sequence_final"
cluster_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/cluster_results"
publish_dir="$VALIDATION_ROOT/imported/utility_foundation"
common_src_dir="$VALIDATION_ROOT/certificates/common"
certificate_src_dir="$VALIDATION_ROOT/certificates/utility_foundation"
fixture_dir="$VALIDATION_ROOT/fixtures/utility_foundation"
prepare_config="$fixture_dir/sum_sequence_prepare_config.json"
mkdir -p "$log_dir" "$cluster_dir" "$publish_dir"

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_before.json" \
  > "$log_dir/baseline_before.log"

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Sum.lean"; then
  echo "forbidden production proof escape in Prosa/Util/Sum.lean" >&2
  exit 1
fi
for path in \
  "$common_src_dir/LogicalRelation.v" \
  "$common_src_dir/SubadditivityNatCorrespondence.v" \
  "$common_src_dir/SumSequenceCorrespondence.v" \
  "$certificate_src_dir/SumSequenceCertificate.v" \
  "$certificate_src_dir/SumSequenceTypeAudit.v" \
  "$certificate_src_dir/SumSequenceAssumptionAudit.v"; do
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
    echo "forbidden certificate proof escape in $path" >&2
    exit 1
  fi
done

work=$(validation_fresh_workdir utility_sum_sequence)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/utility_foundation" \
  "$work/imported" "$work/source/util" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

for module in Prosa/Util/Tactics Prosa/Util/Notation Prosa/Util/Rel \
  Prosa/Util/Nat Prosa/Util/Sum; do
  validation_compile_lean_module "$work" "$module" \
    > "$log_dir/fresh_${module##*/}.log" 2>&1
done
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/utility_foundation/SumSequenceComputationInterface.olean" \
  "$fixture_dir/SumSequenceComputationInterface.lean" \
  > "$log_dir/fresh_interface.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanSumSequenceAudit.lean" \
  > "$log_dir/lean_freeze.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanSumFullAudit.lean" \
  > "$log_dir/lean_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/sum_full_axiom_config.json" \
  --log "$log_dir/lean_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

export LEAN4EXPORT_STATEMENT_ONLY=$(python3 -c \
  'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["statement_only_targets"]))' \
  "$prepare_config")
export LEAN4EXPORT_BODY_THEOREMS=$(python3 -c \
  'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["body_theorem_targets"]))' \
  "$prepare_config")
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
targets=()
while IFS= read -r target; do targets+=("$target"); done < <(
  python3 -c 'import json,sys; c=json.load(open(sys.argv[1])); print("\n".join(c["statement_only_targets"]+c["definition_targets"]+c["body_theorem_targets"]))' \
    "$prepare_config")
"$EXPORTER_ROOT/.lake/build/bin/lean4export" \
  "Validation.fixtures.utility_foundation.SumSequenceComputationInterface" -- \
  "${targets[@]}" > "$work/imported/SumSequence.out" \
  2> "$log_dir/export.log"
[[ -s "$work/imported/SumSequence.out" ]]

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
declarations=$(python3 -c \
  'import json,sys; print(",".join(x.rsplit(".",1)[-1] for x in json.load(open(sys.argv[1]))["statement_only_targets"]))' \
  "$prepare_config")
python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" --source-file util/sum.v \
  --module GeneratedSumSequenceSource --declarations "$declarations" \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.sum \
  --output "$work/source/GeneratedSumSequenceSource.v" \
  --metadata "$work/source/sum_sequence_source_extraction.json" \
  > "$log_dir/source_extraction.log"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedSumSequenceSource.v) \
  > "$log_dir/generated_source_compile.log" 2>&1
cp "$work/source/sum_sequence_source_extraction.json" \
  "$log_dir/source_extraction.json"

cp "$fixture_dir/ImportedSumSequence.v" "$work/imported/ImportedSumSequence.v"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
   99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedSumSequence.v) \
  > "$log_dir/import.log" 2>&1

cp "$common_src_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence,SumSequenceCorrespondence}.v \
  "$work/certificates/"
cp "$certificate_src_dir/"{SumSequenceCertificate,SumSequenceTypeAudit,SumSequenceAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  SumSequenceCorrespondence SumSequenceCertificate SumSequenceTypeAudit \
  SumSequenceAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_SumSequenceAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$certificate_src_dir/sum_sequence_assumption_config.json" \
  --log "$log_dir/assumptions.log" \
  --output "$log_dir/assumption_summary.json" \
  > "$log_dir/assumption_classifier.log"

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" --output "$log_dir/baseline_after.json" \
  > "$log_dir/baseline_after.log"
python3 "$script_dir/publish_utility_cluster.py" \
  --project-root "$PROJECT_ROOT" --validation-root "$VALIDATION_ROOT" \
  --source-root "$SOURCE_ROOT" --exporter-root "$EXPORTER_ROOT" \
  --importer-root "$IMPORTER_ROOT" --work "$work" \
  --config "$certificate_src_dir/sum_sequence_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/sum_sequence.json" \
  > "$log_dir/publication.log"

cp "$work/imported/SumSequence.out" "$publish_dir/SumSequence.out"
cp "$work/imported/ImportedSumSequence.v" "$publish_dir/ImportedSumSequence.v"
cp "$work/imported/ImportedSumSequence.vo" "$publish_dir/ImportedSumSequence.vo"
for module in SumSequenceCorrespondence SumSequenceCertificate \
  SumSequenceTypeAudit SumSequenceAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 "$script_dir/generate_utility_foundation_results.py" \
  > "$log_dir/aggregate_status.log"
(cd "$REPO_ROOT" && git diff --check)

echo "util/sum.v sequence cluster: 19 / 25 ACCEPTED"
echo "fresh work directory: $work"
