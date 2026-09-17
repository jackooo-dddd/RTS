#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")/.." && pwd)
prosa_root=$(cd "$here/.." && pwd)
mathlib_dir=${MATHLIB_DIR:?Set MATHLIB_DIR to Mathlib v4.33.1}
exporter=${LEAN4EXPORT:?Set LEAN4EXPORT to the legacy exporter binary at commit c9f8373}
toolchain=${LEAN_TOOLCHAIN:-leanprover/lean4:v4.33.1}
olean_root="$here/.work/olean"

mkdir -p "$olean_root/Prosa/Behavior" "$olean_root/Prosa/Util" "$here/export"
mathlib_path=$(cd "$mathlib_dir" && lake env printenv LEAN_PATH)
export ELAN_TOOLCHAIN="$toolchain"
export LEAN_PATH="$olean_root:$prosa_root:$mathlib_path"

compile() {
  local module_path=$1
  local source="$prosa_root/$module_path.lean"
  local output="$olean_root/$module_path.olean"
  mkdir -p "$(dirname "$output")"
  lean -R "$prosa_root" -o "$output" "$source"
}

compile Prosa/Behavior/Time
compile Prosa/Behavior/Job
compile Prosa/Util/Notation
compile Prosa/Behavior/Arrival_sequence
compile Prosa/Behavior/Schedule
compile Prosa/Behavior/Service

"$exporter" Prosa.Behavior.Schedule -- \
  Prosa.Behavior.Schedule.ProcessorState.scheduled_in \
  > "$here/export/ScheduledIn.out"
"$exporter" Prosa.Behavior.Service -- \
  Prosa.Behavior.Service.completed_by \
  > "$here/export/CompletedBy.out"

wc -l -c "$here/export/ScheduledIn.out" "$here/export/CompletedBy.out"
