#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")/.." && pwd)
rocq_dir="$here/rocq"
report_dir="$here/reports"
switch_name=${PROSA_OPAM_SWITCH:-prosa-0.6}

if rg -n '\b(Admitted|Axiom|Parameter)\b|\bsorry\b' "$rocq_dir"/*.v; then
  echo "Forbidden proof escape found." >&2
  exit 1
fi

files=(
  Relations.v
  NatBridge.v
  BoolBridge.v
  FiniteBridge.v
  ProcessorStateBridge.v
  CompletedByCertificate.v
  MutationFixtures.v
)

cd "$rocq_dir"
for file in "${files[@]}"; do
  opam exec --switch="$switch_name" -- rocq c "$file"
done
opam exec --switch="$switch_name" -- rocq c AssumptionAudit.v \
  | tee "$report_dir/assumptions.log"

echo "Bridge scaffolding: PASS"
echo "Actual-artifact certificates: BLOCKED (run import_lean.sh for the recorded failure)"
