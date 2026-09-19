#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
prosa_root=$(cd "$validation_root/.." && pwd)
mathlib_dir=${MATHLIB_DIR:-/private/tmp/mathlib4-v4.33.1}
exporter_src=${LEAN4EXPORT_SRC:-/private/tmp/lean4export}
toolchain=${LEAN_TOOLCHAIN:-leanprover/lean4:v4.33.1}
log_dir="$validation_root/reports/logs/${JOB_ARRIVAL_LOG_EXPERIMENT:-experiment11}"
artifact="$validation_root/export/JobArrivalMinimal.out"
mkdir -p "$validation_root/.work" "$validation_root/export" "$log_dir"
build=$(mktemp -d "$validation_root/.work/clean_job_arrival_build.XXXXXX")

ELAN_TOOLCHAIN="$toolchain" lake -d "$exporter_src" build lean4export >/dev/null
exporter="$exporter_src/.lake/build/bin/lean4export"
mathlib_path=$(cd "$mathlib_dir" && lake env printenv LEAN_PATH)
export ELAN_TOOLCHAIN="$toolchain"
export LEAN_PATH="$build:$prosa_root:$mathlib_path"

for module in Prosa/Behavior/Time Prosa/Behavior/Job; do
  mkdir -p "$build/$(dirname "$module")"
  lean -R "$prosa_root" -o "$build/$module.olean" "$prosa_root/$module.lean"
done

export LEAN4EXPORT_STATEMENT_ONLY=
export LEAN4EXPORT_BODY_THEOREMS=
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
"$exporter" Prosa.Behavior.Job -- \
  Prosa.Behavior.Time.instant \
  Prosa.Behavior.Job.JobArrival \
  Prosa.Behavior.Job.JobArrival.job_arrival > "$artifact" \
  2> "$log_dir/job_arrival_minimal_export.log"

{
  echo "Lean toolchain: $toolchain"
  echo "Fresh build: $build"
  shasum -a 256 "$prosa_root/Prosa/Behavior/Time.lean"
  shasum -a 256 "$prosa_root/Prosa/Behavior/Job.lean"
  shasum -a 256 "$artifact"
} > "$log_dir/job_arrival_minimal_manifest.log"
cat "$log_dir/job_arrival_minimal_manifest.log"
