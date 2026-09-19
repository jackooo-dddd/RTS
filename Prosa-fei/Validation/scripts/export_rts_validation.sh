#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
prosa_root=$(cd "$validation_root/.." && pwd)
mathlib_dir=${MATHLIB_DIR:-/private/tmp/mathlib4-v4.33.1}
exporter_src=${LEAN4EXPORT_SRC:-/private/tmp/lean4export}
toolchain=${LEAN_TOOLCHAIN:-leanprover/lean4:v4.33.1}
olean_root="$validation_root/.work/rts_olean"
log_dir="$validation_root/reports/logs"

mkdir -p "$olean_root/Prosa/Util" "$log_dir" "$validation_root/export"

if ! rg -q 'Statement-validation mode' "$exporter_src/Export.lean"; then
  patch -d "$exporter_src" -p1 --forward \
    < "$validation_root/patches/lean4export-scheduled-at-statement-only.patch"
fi
ELAN_TOOLCHAIN="$toolchain" lake -d "$exporter_src" build lean4export
exporter="$exporter_src/.lake/build/bin/lean4export"

mathlib_path=$(cd "$mathlib_dir" && lake env printenv LEAN_PATH)
export ELAN_TOOLCHAIN="$toolchain"
export LEAN_PATH="$olean_root:$prosa_root:$mathlib_path"

# The production Prosa.Util.All file is only an import aggregator.  The shim
# omits unrelated modules with Mathlib-drift proof failures and declares no
# replacement object.
lean -R "$validation_root/lean_shims" \
  -o "$olean_root/Prosa/Util/All.olean" \
  "$validation_root/lean_shims/Prosa/Util/All.lean"

build_module() {
  local module=$1 rel source output dep
  rel=${module//./\/}
  source="$prosa_root/$rel.lean"
  output="$olean_root/$rel.olean"
  [[ -f "$output" ]] && return 0
  [[ -f "$source" ]] || return 0
  while IFS= read -r dep; do
    [[ "$dep" == Prosa.* ]] && build_module "$dep"
  done < <(awk '$1 == "import" { for (i=2; i<=NF; i++) print $i }' "$source")
  mkdir -p "$(dirname "$output")"
  lean -R "$prosa_root" -o "$output" "$source"
}

build_module Prosa.Analysis.Facts.Model.Ideal_schedule
build_module Prosa.Validation.IdealScheduledInFixture

roots=(
  Prosa.Behavior.Time.instant
  Prosa.Behavior.Time.duration
  Prosa.Behavior.Job.work
  Prosa.Behavior.Job.JobCost.job_cost
  Prosa.Behavior.Job.JobArrival.job_arrival
  Prosa.Behavior.Job.JobDeadline.job_deadline
  Prosa.Behavior.Arrival_sequence.arrival_sequence
  Prosa.Behavior.Arrival_sequence.arrivals_at
  Prosa.Behavior.Arrival_sequence.arrives_at
  Prosa.Behavior.Arrival_sequence.arrives_in
  Prosa.Behavior.Arrival_sequence.has_arrived
  Prosa.Behavior.Arrival_sequence.arrived_before
  Prosa.Behavior.Arrival_sequence.arrived_between
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times
  Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence
  Prosa.Behavior.Arrival_sequence.arrivals_between
  Prosa.Behavior.Arrival_sequence.arrivals_up_to
  Prosa.Behavior.Arrival_sequence.arrivals_before
  Prosa.Behavior.Schedule.ProcessorState.scheduled_in
  Prosa.Validation.ideal_scheduled_in
  Prosa.Behavior.Service.scheduled_at
  Prosa.Validation.ideal_scheduled_at
  Prosa.Analysis.Facts.Model.Ideal_schedule.scheduled_at_def
  Classical.propDecidable
)

"$exporter" \
  Prosa.Analysis.Facts.Model.Ideal_schedule \
  Prosa.Validation.IdealScheduledInFixture -- "${roots[@]}" \
  > "$validation_root/export/RTSValidation.out" \
  2> "$log_dir/export_rts_validation.log"

rg -q '#NS .* scheduled_at_def$' "$validation_root/export/RTSValidation.out"
wc -l -c "$validation_root/export/RTSValidation.out"
