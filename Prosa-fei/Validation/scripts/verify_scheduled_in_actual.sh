#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
rocq_dir="$validation_root/rocq"
report_dir="$validation_root/reports"
switch_name=${IMPORT_OPAM_SWITCH:-rocq93rc1}
importer_src=${ROCQLI_SRC:?Set ROCQLI_SRC to the compatible rocq-lean-import source tree}
switch_prefix=$(opam var --switch="$switch_name" prefix)
prosa_src=${PROSA_ROCQ_SRC:-$switch_prefix/.opam-switch/sources/rocq-prosa.0.6}

if [[ ! -f "$prosa_src/behavior/schedule.v" ]]; then
  echo "Prosa source not found at $prosa_src" >&2
  exit 1
fi

if rg -n '\b(Admitted|Axiom)\b|\bsorry\b' \
    "$rocq_dir/ProcessorStateBridge.v" \
    "$rocq_dir/ScheduledInActualAudit.v" \
    "$rocq_dir/ScheduledInPolarityMutation.v"; then
  echo "Forbidden proof escape found." >&2
  exit 1
fi

if [[ ${REIMPORT:-0} == 1 ]]; then
  ROCQLI_SRC="$importer_src" IMPORT_OPAM_SWITCH="$switch_name" \
    "$validation_root/scripts/import_lean.sh" ImportedScheduled93.v
fi

if [[ ! -f "$rocq_dir/ImportedScheduled93.vo" ]]; then
  echo "ImportedScheduled93.vo is absent; rerun with REIMPORT=1." >&2
  exit 1
fi

rocq_compile() {
  opam exec --switch="$switch_name" -- rocq c \
    -R "$prosa_src" prosa \
    -Q "$importer_src/src" LeanImport \
    -I "$importer_src/src" \
    "$1"
}

cd "$rocq_dir"
rocq_compile Relations.v
rocq_compile FiniteBridge.v
rocq_compile ProcessorStateBridge.v
rocq_compile ScheduledInActualAudit.v \
  | tee "$report_dir/scheduled_in_actual_assumptions.log"
rocq_compile ScheduledInPolarityMutation.v \
  | tee "$report_dir/scheduled_in_mutation.log"

echo "scheduled_in actual-artifact certificate: CONDITIONAL PASS"
echo "scheduled_in polarity mutation rejection: PASS"
