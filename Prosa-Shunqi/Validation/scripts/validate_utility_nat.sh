#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/nat"
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

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Nat.lean"; then
  echo "forbidden production proof escape in Prosa/Util/Nat.lean" >&2
  exit 1
fi
for path in \
  "$common_src_dir/LogicalRelation.v" \
  "$common_src_dir/SubadditivityNatCorrespondence.v" \
  "$common_src_dir/NatSubCorrespondence.v" \
  "$certificate_src_dir/NatCertificate.v" \
  "$certificate_src_dir/NatAssumptionAudit.v"; do
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

work=$(validation_fresh_workdir utility_nat)
mkdir -p "$work/olean/Prosa/Util" "$work/source/util" \
  "$work/imported" "$work/certificates"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

# Compile every production dependency used by Nat into this new directory.
# The project tree's old .olean files therefore cannot satisfy these imports.
validation_compile_lean_module "$work" "Prosa/Util/Tactics" \
  > "$log_dir/fresh_Tactics.log" 2>&1
validation_compile_lean_module "$work" "Prosa/Util/Nat" \
  > "$log_dir/fresh_Nat.log" 2>&1
lean -DautoImplicit=false "$fixture_dir/LeanNatAudit.lean" \
  > "$log_dir/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$fixture_dir/nat_axiom_config.json" \
  --log "$log_dir/lean_freeze_and_axioms.log" \
  --output "$log_dir/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"

# Export the exact freshly compiled theorem types, omitting only proof bodies.
export LEAN4EXPORT_BODY_THEOREMS=
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
export LEAN4EXPORT_STATEMENT_ONLY=$'Prosa.Util.Nat.subnACA\nProsa.Util.Nat.leq_subRL_impl'
"$EXPORTER_ROOT/.lake/build/bin/lean4export" "Prosa.Util.Nat" -- \
  Prosa.Util.Nat.subnACA Prosa.Util.Nat.leq_subRL_impl \
  > "$work/imported/Nat.out" 2> "$log_dir/export_Nat.log"

# Compile byte-identical official sources; only the already audited Rocq-9.3
# tactic compatibility patch is applied to the validation copy of tactics.v.
cp "$SOURCE_ROOT/util/tactics.v" "$work/source/util/tactics.v"
cp "$SOURCE_ROOT/util/nat.v" "$work/source/util/nat.v"
[[ $(validation_sha256 "$work/source/util/tactics.v") == \
   b55a2ee4f5efbd6e8593b0c95d6ae42414517a4f2cc0f4ccf90488371c2a7eff ]]
[[ $(validation_sha256 "$work/source/util/nat.v") == \
   6f1c4f84dd87d461fad3f617325e1ff7acd7c55a474143eede5ffe2de08c3b80 ]]
(cd "$work/source" && patch -p1 --forward --batch < \
  "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch") \
  > "$log_dir/source_patch_tactics.log" 2>&1
for source in tactics nat; do
  (cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
    rocq c -R "$work/source" prosa "util/$source.v") \
    > "$log_dir/official_${source}_compile.log" 2>&1
done

# Import the newly exported Nat artifact.  The already accepted
# Subadditivity artifact supplies the representation against which the common
# Nat relation was proved; its pinned hash is checked before use.
cp "$publish_dir/ImportedNat.v" "$work/imported/"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
   99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedNat.v) \
  > "$log_dir/import_Nat.log" 2>&1

cp "$common_src_dir/"{PropSPropFoundation,LogicalRelation,SubadditivityNatCorrespondence,NatSubCorrespondence}.v \
  "$work/certificates/"
cp "$certificate_src_dir/"{NatCertificate,NatAssumptionAudit}.v \
  "$work/certificates/"
for module in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  NatSubCorrespondence NatCertificate NatAssumptionAudit; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$log_dir/rocq_${module}.log" 2>&1
done
cp "$log_dir/rocq_NatAssumptionAudit.log" "$log_dir/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$certificate_src_dir/nat_assumption_config.json" \
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
  --config "$certificate_src_dir/nat_cluster_config.json" \
  --freeze-log "$log_dir/lean_freeze_and_axioms.log" \
  --lean-axioms "$log_dir/lean_axiom_summary.json" \
  --assumptions "$log_dir/assumption_summary.json" \
  --baseline "$log_dir/baseline_after.json" \
  --output "$cluster_dir/nat.json" \
  > "$log_dir/publication.log"

# Publish canonical artifacts only after all checks and content-addressed
# result generation have succeeded.
cp "$work/imported/Nat.out" "$publish_dir/Nat.out"
cp "$work/imported/ImportedNat.vo" "$publish_dir/ImportedNat.vo"
for module in NatSubCorrespondence NatCertificate NatAssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done

python3 "$script_dir/generate_utility_foundation_results.py" \
  > "$log_dir/aggregate_status.log"

(cd "$REPO_ROOT" && git diff --check)

echo "util/nat.v = ACCEPTED_V06_FILE"
echo "accepted declarations: 2 / 2"
echo "fresh work directory: $work"
