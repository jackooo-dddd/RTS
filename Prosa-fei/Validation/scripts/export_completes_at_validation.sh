#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
prosa_root=$(cd "$validation_root/.." && pwd)
mathlib_dir=${MATHLIB_DIR:-/private/tmp/mathlib4-v4.33.1}
exporter_src=${LEAN4EXPORT_SRC:-/private/tmp/lean4export}
toolchain=${LEAN_TOOLCHAIN:-leanprover/lean4:v4.33.1}
artifact="$validation_root/export/CompletesAtValidation.out"
log_dir="$validation_root/reports/logs/${COMPLETES_LOG_EXPERIMENT:-experiment10}"
fixture="$validation_root/lean_fixtures/completes_at_corrected/CompletesAtCorrected.lean"

mkdir -p "$validation_root/.work" "$validation_root/export" "$log_dir"
olean_root=$(mktemp -d "$validation_root/.work/clean_completes_at_build.XXXXXX")

if ! rg -q 'def statementOnlyTheorem' "$exporter_src/Export.lean"; then
  patch -d "$exporter_src" -p1 --forward \
    < "$validation_root/patches/lean4export-generic-statement-only.patch"
elif ! rg -q 'LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS' "$exporter_src/Export.lean"; then
  echo "lean4export has an older validation patch; restore pristine Export.lean and rerun" >&2
  exit 1
fi
ELAN_TOOLCHAIN="$toolchain" lake -d "$exporter_src" build lean4export
exporter="$exporter_src/.lake/build/bin/lean4export"
mathlib_path=$(cd "$mathlib_dir" && lake env printenv LEAN_PATH)
export ELAN_TOOLCHAIN="$toolchain"
export LEAN_PATH="$olean_root:$prosa_root:$mathlib_path"

build_module() {
  local module=$1 rel source output dep
  rel=${module//./\/}
  source="$prosa_root/$rel.lean"
  output="$olean_root/$rel.olean"
  [[ -f "$output" ]] && return 0
  while IFS= read -r dep; do
    [[ "$dep" == Prosa.* ]] && build_module "$dep"
  done < <(awk '$1 == "import" { for (i=2; i<=NF; i++) print $i }' "$source")
  mkdir -p "$(dirname "$output")"
  lean -R "$prosa_root" -o "$output" "$source"
}

build_module Prosa.Behavior.Service
mkdir -p "$olean_root/Prosa/Validation/CompletesAt"
lean -R "$prosa_root" \
  -o "$olean_root/Prosa/Validation/CompletesAt/CompletesAtCorrected.olean" \
  "$fixture"

export LEAN4EXPORT_STATEMENT_ONLY=
export LEAN4EXPORT_BODY_THEOREMS=
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=$'Prosa.Validation.CompletesAt.production_completes_at_zero=Prosa.Validation.CompletesAt.production_completes_at_zero_normal_form=Prosa.Validation.CompletesAt.production_completes_at_zero_defeq\nProsa.Validation.CompletesAt.corrected_completes_at_zero=Prosa.Validation.CompletesAt.corrected_completes_at_zero_normal_form=Prosa.Validation.CompletesAt.corrected_completes_at_zero_defeq'

"$exporter" Prosa.Validation.CompletesAt.CompletesAtCorrected -- \
  Prosa.Validation.CompletesAt.production_completes_at_zero \
  Prosa.Validation.CompletesAt.corrected_completes_at_zero \
  Prosa.Validation.CompletesAt.completes_at_formula \
  > "$artifact" 2> "$log_dir/completes_at_export.log"

{
  git_prefix=$(git -C "$prosa_root" rev-parse --show-prefix)
  echo "Lean toolchain: $toolchain"
  echo "Repository commit: $(git -C "$prosa_root" rev-parse HEAD)"
  echo "Frozen production tree: $(git -C "$prosa_root" rev-parse "HEAD:${git_prefix}Prosa")"
  echo "Fresh build directory: $olean_root"
  echo "Production completes_at source: $prosa_root/Prosa/Behavior/Service.lean"
  shasum -a 256 "$prosa_root/Prosa/Behavior/Service.lean"
  echo "Validation-only fixture: $fixture"
  shasum -a 256 "$fixture"
  echo "Kernel guard: Prosa.Validation.CompletesAt.completes_at_corrected_formula_defeq (compiled proof: rfl)"
  echo "Artifact: $artifact"
  wc -l -c "$artifact"
  shasum -a 256 "$artifact"
  echo "Normalization audit:"
  cat "$log_dir/completes_at_export.log"
} > "$log_dir/completes_at_export_manifest.log"

cat "$log_dir/completes_at_export_manifest.log"
