#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
prosa_root=$(cd "$validation_root/.." && pwd)
mathlib_dir=${MATHLIB_DIR:-/private/tmp/mathlib4-v4.33.1}
exporter_src=${LEAN4EXPORT_SRC:-/private/tmp/lean4export}
toolchain=${LEAN_TOOLCHAIN:-leanprover/lean4:v4.33.1}
log_dir="$validation_root/reports/logs"
mapping="$validation_root/mapping/rts_validation_targets.yaml"

mkdir -p "$validation_root/.work" "$log_dir" "$validation_root/export"
if [[ -n ${LEAN_VALIDATION_BUILD_DIR:-} ]]; then
  olean_root=$LEAN_VALIDATION_BUILD_DIR
  mkdir -p "$olean_root"
else
  olean_root=$(mktemp -d "$validation_root/.work/clean_rts_lean_build.XXXXXX")
fi
mkdir -p "$olean_root/Prosa/Util"

if ! rg -q 'def statementOnlyTheorem' "$exporter_src/Export.lean"; then
  patch -d "$exporter_src" -p1 --forward \
    < "$validation_root/patches/lean4export-generic-statement-only.patch"
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

export_modules=()
while IFS= read -r theorem_module; do
  [[ -n "$theorem_module" ]] || continue
  build_module "$theorem_module"
  export_modules+=("$theorem_module")
done < <(python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root /dev/null --list-lean-modules)

mkdir -p "$olean_root/Prosa/Validation"
lean -R "$prosa_root" \
  -o "$olean_root/Prosa/Validation/IdealScheduledInFixture.olean" \
  "$validation_root/lean/IdealScheduledInFixture.lean"
export_modules+=(Prosa.Validation.IdealScheduledInFixture)

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
  Classical.propDecidable
)

theorem_names=()
while IFS= read -r theorem_name; do
  [[ -n "$theorem_name" ]] || continue
  theorem_names+=("$theorem_name")
  roots+=("$theorem_name")
done < <(python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root /dev/null --list-lean-theorems)

statement_only=$(printf '%s\n' "${theorem_names[@]}")
export LEAN4EXPORT_STATEMENT_ONLY="$statement_only"

"$exporter" \
  "${export_modules[@]}" -- "${roots[@]}" \
  > "$validation_root/export/RTSValidation.out" \
  2> "$log_dir/export_rts_validation.log"

{
  echo "Lean 4 toolchain: $toolchain"
  echo "Repository commit: $(git -C "$prosa_root" rev-parse HEAD)"
  git_prefix=$(git -C "$prosa_root" rev-parse --show-prefix)
  echo "Lean source tree: $(git -C "$prosa_root" rev-parse "HEAD:${git_prefix}Prosa")"
  echo "Fresh build directory: $olean_root"
  echo "Exporter: $exporter"
  echo "Statement-only theorems read from $mapping:"
  printf '  %s\n' "${theorem_names[@]}"
  echo "Artifact namespace evidence:"
  for theorem_name in "${theorem_names[@]}"; do
    short_name=${theorem_name##*.}
    rg '#NS .* '"$short_name"'$' "$validation_root/export/RTSValidation.out"
  done
  shasum -a 256 "$validation_root/export/RTSValidation.out"
  echo "Compiled Lean source hashes:"
  for module in "${export_modules[@]}"; do
    [[ "$module" == Prosa.Validation.* ]] && continue
    rel=${module//./\/}
    shasum -a 256 "$prosa_root/$rel.lean"
  done
  shasum -a 256 "$validation_root/lean/IdealScheduledInFixture.lean"
} > "$log_dir/lean_statement_export_manifest.log"

for theorem_name in "${theorem_names[@]}"; do
  short_name=${theorem_name##*.}
  rg -q '#NS .* '"$short_name"'$' "$validation_root/export/RTSValidation.out"
done
wc -l -c "$validation_root/export/RTSValidation.out"
