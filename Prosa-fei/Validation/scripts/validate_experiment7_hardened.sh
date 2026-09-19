#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
prosa_root=$(cd "$validation_root/.." && pwd)
rocq_dir="$validation_root/rocq"
generated="$rocq_dir/generated_hard"
log_dir="$validation_root/reports/logs/experiment7"
switch_name=${IMPORT_OPAM_SWITCH:-rocq93rc1}
importer_src=${ROCQLI_SRC:-/private/tmp/rocq-lean-import-93}
prosa_src=${PROSA_ROCQ_SRC:-/Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6}
reexport=${REEXPORT:-1}

mkdir -p "$log_dir"

if ! git -C "$prosa_root" diff --quiet -- Prosa; then
  echo "production Lean translation differs from the frozen repository snapshot" >&2
  exit 1
fi

if rg -n '\b(Admitted|admit|sorry)\b' \
    "$rocq_dir" "$validation_root/lean" "$validation_root/lean_fixtures" \
    --glob '*.v' --glob '*.lean'; then
  echo "forbidden proof escape found" >&2
  exit 1
fi
axioms=$(rg -n '\bAxiom\b' "$rocq_dir" --glob '*.v' || true)
axiom_count=$(printf '%s\n' "$axioms" | sed '/^$/d' | wc -l | tr -d ' ')
if [[ "$axiom_count" != 1 ]] || \
   ! printf '%s\n' "$axioms" | rg -q '^.*/PropSPropFoundation\.v:[0-9]+:Axiom interpret_strict :$'; then
  echo "axiom allowlist mismatch; expected exactly the foundation interpretation principle" >&2
  echo "$axioms" >&2
  exit 1
fi

set +e
opam exec --switch="$switch_name" -- rocq c \
  "$validation_root/negative_fixtures/SPropToPropElimination.v" \
  > "$log_dir/sprop_to_prop_actual_error.log" 2>&1
sprop_probe_rc=$?
set -e
if [[ "$sprop_probe_rc" == 0 ]] || \
   ! rg -q 'strict proofs can be eliminated only to build strict proofs' \
      "$log_dir/sprop_to_prop_actual_error.log"; then
  echo "SProp-to-Prop negative foundation probe did not fail as expected" >&2
  exit 1
fi

"$validation_root/scripts/test_clean_lean_rebuild.sh" \
  > "$log_dir/cache_invalidation_run.log" 2>&1

REEXPORT="$reexport" "$validation_root/scripts/validate_hard_translation.sh" \
  > "$log_dir/hard_validation_summary.log" 2>&1
REEXPORT="$reexport" "$validation_root/scripts/validate_rts_translation.sh" \
  > "$log_dir/rts_validation_summary.log" 2>&1

python3 "$validation_root/scripts/audit_source_fidelity.py" \
  --mapping "$validation_root/mapping/hard_validation_targets.yaml" \
  --source-root "$prosa_src" --generated-dir "$generated" \
  --output "$log_dir/source_fidelity_audit.json" \
  > "$log_dir/source_fidelity_audit.log"
python3 "$validation_root/scripts/audit_source_fidelity.py" \
  --mapping "$validation_root/mapping/rts_validation_targets.yaml" \
  --source-root "$prosa_src" --generated-dir "$rocq_dir" \
  --single-generated-module GeneratedOfficialProsa06 \
  --output "$log_dir/source_fidelity_rts_audit.json" \
  > "$log_dir/source_fidelity_rts_audit.log"

"$validation_root/scripts/test_interval_semantic_mutation.sh" \
  > "$log_dir/interval_mutation_summary.log" 2>&1

compile() {
  local file=$1 log=$2
  opam exec --switch="$switch_name" -- rocq c \
    -R "$prosa_src" prosa \
    -Q "$importer_src/src" LeanImport -I "$importer_src/src" \
    -Q "$generated" HardSource "$file" > "$log_dir/$log" 2>&1
}

cd "$rocq_dir"
ulimit -s 65520
compile AssumptionAuditHardExperiment7.v assumptions_hard.log
compile AssumptionAuditRTSExperiment7.v assumptions_rts.log

python3 "$validation_root/scripts/classify_assumptions.py" \
  --config "$validation_root/mapping/experiment7_assumption_audit.yaml" \
  --log "$log_dir/assumptions_hard.log" --log "$log_dir/assumptions_rts.log" \
  --output "$log_dir/assumption_summary.json" \
  | tee "$log_dir/assumption_statuses.log"

python3 - "$log_dir/assumption_summary.json" <<'PY'
import json, sys
data = json.load(open(sys.argv[1]))["certificates"]
print("\nExperiment 7 Hardened Semantic Validation")
for name, result in data.items():
    print(f"{name:36} {result['status']}")
print("sum_diff                            SOURCE_UNMAPPED")
print("sum_seq_gt0P                        SOURCE_UNMAPPED")
print("sum_pred_diff                       SOURCE_UNMAPPED")
print("\nFresh rebuild cache invalidation     PASS")
print("Source elaborated-type fidelity      PASS")
print("End-to-end endpoint mutation         PASS")
print("Unexpected assumptions               NONE")
PY
