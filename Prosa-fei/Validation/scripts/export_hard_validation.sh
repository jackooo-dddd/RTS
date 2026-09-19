#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
prosa_root=$(cd "$validation_root/.." && pwd)
mapping="$validation_root/mapping/hard_validation_targets.yaml"
mathlib_dir=${MATHLIB_DIR:-/private/tmp/mathlib4-v4.33.1}
exporter_src=${LEAN4EXPORT_SRC:-/private/tmp/lean4export}
toolchain=${LEAN_TOOLCHAIN:-leanprover/lean4:v4.33.1}
olean_root="$validation_root/.work/hard_olean"
log_dir="$validation_root/reports/logs"
log_prefix=${HARD_LOG_PREFIX:-experiment5}
artifact=${HARD_ARTIFACT:-$validation_root/export/HardValidation.out}
target_args=()
if [[ -n ${HARD_TARGET_KEYS:-} ]]; then
  target_args=(--target-keys "$HARD_TARGET_KEYS")
fi

mkdir -p "$olean_root/Prosa/Util" "$log_dir" "$validation_root/export"

if ! rg -q 'def statementOnlyTheorem' "$exporter_src/Export.lean"; then
  patch -d "$exporter_src" -p1 --forward \
    < "$validation_root/patches/lean4export-generic-statement-only.patch"
fi
ELAN_TOOLCHAIN="$toolchain" lake -d "$exporter_src" build lean4export
exporter="$exporter_src/.lake/build/bin/lean4export"

mathlib_path=$(cd "$mathlib_dir" && lake env printenv LEAN_PATH)
export ELAN_TOOLCHAIN="$toolchain"
export LEAN_PATH="$olean_root:$prosa_root:$mathlib_path"

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

modules=()
while IFS= read -r module; do
  [[ -n "$module" ]] || continue
  build_module "$module"
  modules+=("$module")
done < <(python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root /dev/null "${target_args[@]}" --list-lean-modules)

roots=()
while IFS= read -r declaration; do
  [[ -n "$declaration" ]] && roots+=("$declaration")
done < <(python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root /dev/null "${target_args[@]}" --list-lean-targets)

theorems=()
while IFS= read -r declaration; do
  [[ -n "$declaration" ]] && theorems+=("$declaration")
done < <(python3 "$validation_root/scripts/extract_rocq_declarations.py" \
  --mapping "$mapping" --source-root /dev/null "${target_args[@]}" --list-lean-theorems)
export LEAN4EXPORT_STATEMENT_ONLY
if [[ ${HARD_ALL_THEOREMS_STATEMENT_ONLY:-0} == 1 ]]; then
  LEAN4EXPORT_STATEMENT_ONLY='*'
else
  LEAN4EXPORT_STATEMENT_ONLY=$(printf '%s\n' "${theorems[@]}")
fi

"$exporter" "${modules[@]}" -- "${roots[@]}" > "$artifact" \
  2> "$log_dir/${log_prefix}_export_hard_validation.log"

{
  echo "Lean toolchain: $toolchain"
  echo "Mapping: $mapping"
  echo "Modules:"
  printf '  %s\n' "${modules[@]}"
  echo "Statement-only theorems:"
  printf '  %s\n' "${theorems[@]}"
  echo "Artifact: $artifact"
  wc -l -c "$artifact"
  shasum -a 256 "$artifact"
} > "$log_dir/${log_prefix}_lean_export_manifest.log"

cat "$log_dir/${log_prefix}_lean_export_manifest.log"
