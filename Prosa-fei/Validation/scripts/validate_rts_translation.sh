#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
rocq_dir="$validation_root/rocq"
log_dir="$validation_root/reports/logs"
switch_name=${IMPORT_OPAM_SWITCH:-rocq93rc1}
importer_src=${ROCQLI_SRC:-/private/tmp/rocq-lean-import-93}
switch_prefix=$(opam var --switch="$switch_name" prefix)
prosa_src=${PROSA_ROCQ_SRC:-/Users/shunqiwang/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6}
mapping="$validation_root/mapping/rts_validation_targets.yaml"

mkdir -p "$log_dir"

if [[ ${REEXPORT:-0} == 1 ]]; then
  "$validation_root/scripts/export_rts_validation.sh"
fi

artifact="$validation_root/export/RTSValidation.out"
[[ -s "$artifact" ]] || { echo "missing $artifact" >&2; exit 1; }
while IFS= read -r theorem_name; do
  [[ -n "$theorem_name" ]] || continue
  short_name=${theorem_name##*.}
  rg -q '#NS .* '"$short_name"'$' "$artifact"
done < <(python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root /dev/null --list-lean-theorems)

python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root "$prosa_src" \
  --output "$rocq_dir/GeneratedOfficialProsa06.v" \
  --metadata "$log_dir/source_fidelity.json"

# No escape hatch is permitted except the one named and isolated Prop/SProp
# trust boundary.
if rg -n '\b(Admitted|admit)\b|\bsorry\b' \
    "$validation_root/rocq" "$validation_root/lean"; then
  echo "forbidden proof escape found" >&2
  exit 1
fi
axioms=$(rg -n '\bAxiom\b' "$validation_root/rocq" --glob '*.v' || true)
if [[ -n "$axioms" ]] && echo "$axioms" | rg -v 'PropSPropBridge\.v:.*prop_sprop_trusted_elim' >/dev/null; then
  echo "unexpected Axiom outside PropSPropBridge.v" >&2
  echo "$axioms" >&2
  exit 1
fi

compile() {
  local file=$1
  opam exec --switch="$switch_name" -- rocq c \
    -R "$prosa_src" prosa \
    -Q "$importer_src/src" LeanImport -I "$importer_src/src" \
    "$file"
}

cd "$rocq_dir"

# The legacy importer uses deep native recursion on this artifact.
ulimit -s 65520
compile ImportedEasy93.v > "$log_dir/import_rts_canonical_rocq93.log" 2>&1

files=(
  Relations.v
  FiniteBridge.v
  PropSPropBridge.v
  ImportedNatBridge.v
  ProcessorStateBridge.v
  EqTypeBridge.v
  ImportedListBridge.v
  ImportedNatOrderBridge.v
  TimeJobCertificates.v
  ArrivalSequenceCertificates.v
  ArrivalTimeCertificates.v
  IdealScheduledInCertificate.v
  ScheduledAtCertificate.v
  GeneratedOfficialProsa06.v
  RTSTheoremCertificate.v
  ScheduledInPolarityMutation.v
)

for file in "${files[@]}"; do
  compile "$file" > "$log_dir/validate_${file%.v}.log" 2>&1
done

echo "RTS Translation Validation"
echo
echo "instant                  CERTIFIED"
echo "duration                 CERTIFIED"
echo "work                     CERTIFIED"
echo "job_cost                 PARAMETRICALLY_CERTIFIED"
echo "job_arrival              PARAMETRICALLY_CERTIFIED"
echo "job_deadline             PARAMETRICALLY_CERTIFIED"
echo "arrival_sequence         PARAMETRICALLY_CERTIFIED"
echo "arrivals_at              PARAMETRICALLY_CERTIFIED"
echo "arrives_at               PARAMETRICALLY_CERTIFIED"
echo "has_arrived              PARAMETRICALLY_CERTIFIED"
echo "arrived_before           PARAMETRICALLY_CERTIFIED"
echo "arrived_between          PARAMETRICALLY_CERTIFIED"
echo "scheduled_in             CERTIFIED (Ideal)"
echo "scheduled_at             CERTIFIED (Ideal)"
echo "scheduled_in_def theorem CERTIFIED_WITH_PROP_SPROP_BRIDGE"
echo "scheduled_at_def theorem CERTIFIED_WITH_PROP_SPROP_BRIDGE"
echo
echo "Mutation Detection"
echo "scheduled_in polarity    PASS (rejected)"
echo
echo "Overall: 16 / 16 selected target declarations semantically validated"
echo "Logs: $log_dir"
