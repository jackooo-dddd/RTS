#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
mathlib_dir=${MATHLIB_DIR:-/private/tmp/mathlib4-v4.33.1}
exporter_src=${LEAN4EXPORT_SRC:-/private/tmp/lean4export}
toolchain=${LEAN_TOOLCHAIN:-leanprover/lean4:v4.33.1}
work=$(mktemp -d "$validation_root/.work/interval_mutation.XXXXXX")
build="$work/build"
source="$validation_root/lean_fixtures/interval_mutation/Validation/IntervalMutationFixture.lean"
artifact="$validation_root/export/Experiment7IntervalMutation.out"
log="$validation_root/reports/logs/experiment7/interval_mutation_export.log"
mkdir -p "$build/Validation" "$(dirname "$artifact")" "$(dirname "$log")"

mathlib_path=$(cd "$mathlib_dir" && lake env printenv LEAN_PATH)
export ELAN_TOOLCHAIN="$toolchain"
export LEAN_PATH="$build:$mathlib_path"
lean -o "$build/Validation/IntervalMutationFixture.olean" "$source"

exporter="$exporter_src/.lake/build/bin/lean4export"
[[ -x "$exporter" ]] || lake -d "$exporter_src" build lean4export
export LEAN4EXPORT_STATEMENT_ONLY='*'
"$exporter" Validation.IntervalMutationFixture -- \
  Validation.IntervalMutationFixture.originalIcoSum \
  Validation.IntervalMutationFixture.mutatedIccSum \
  Validation.IntervalMutationFixture.positiveControlSum > "$artifact"

{
  echo "toolchain=$toolchain"
  echo "fresh_build_directory=$build"
  echo "source_sha256=$(shasum -a 256 "$source" | awk '{print $1}')"
  echo "artifact_sha256=$(shasum -a 256 "$artifact" | awk '{print $1}')"
} > "$log"
cat "$log"
