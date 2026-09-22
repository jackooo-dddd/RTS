#!/usr/bin/env bash

# Shared fail-closed infrastructure for Prosa v0.6 semantic validation.
# Callers must enable `set -euo pipefail` before sourcing this file.

validation_common_init() {
  local caller_script_dir=$1
  VALIDATION_ROOT=$(cd "$caller_script_dir/.." && pwd)
  PROJECT_ROOT=$(cd "$VALIDATION_ROOT/.." && pwd)
  REPO_ROOT=$(cd "$PROJECT_ROOT/.." && pwd)
  LEAN_TOOLCHAIN_EXPECTED=leanprover/lean4:v4.33.1
  MATHLIB_COMMIT_EXPECTED=0df444a360eaa60ab8c11dca51a86af692955474
  PROSA_COMMIT_EXPECTED=414e66760333eaa4ef78c685bcf53291c527a548
  PROSA_TREE_EXPECTED=7d7e94c731f7eefde4ca738310d4cafdd7bebdf0
  ROCQ_SWITCH=${IMPORT_OPAM_SWITCH:-rocq93rc1}

  local source_override=${PROSA_V06_SOURCE_ROOT:-}
  if [[ -n "$source_override" ]]; then
    SOURCE_ROOT=$(PROSA_V06_SOURCE_ROOT="$source_override" \
      "$VALIDATION_ROOT/scripts/ensure_pinned_v06_source.sh")
  else
    SOURCE_ROOT=$("$VALIDATION_ROOT/scripts/ensure_pinned_v06_source.sh")
  fi

  "$VALIDATION_ROOT/tooling/setup_validation_tooling.sh" >/dev/null
  EXPORTER_ROOT=${LEAN4EXPORT_SRC:-"$VALIDATION_ROOT/.work/tooling/lean4export"}
  IMPORTER_ROOT=${ROCQLI_SRC:-"$VALIDATION_ROOT/.work/tooling/rocq-lean-import"}
  if [[ $(git -C "$SOURCE_ROOT" rev-parse HEAD) != "$PROSA_COMMIT_EXPECTED" ]]; then
    echo "authoritative Prosa commit mismatch" >&2; return 1
  fi
  if [[ $(git -C "$SOURCE_ROOT" rev-parse HEAD^{tree}) != "$PROSA_TREE_EXPECTED" ]]; then
    echo "authoritative Prosa tree mismatch" >&2; return 1
  fi
  if [[ -n $(git -C "$SOURCE_ROOT" status --porcelain --untracked-files=all) ]]; then
    echo "authoritative Prosa worktree is not clean" >&2; return 1
  fi
  if [[ $(tr -d '\r\n' < "$PROJECT_ROOT/lean-toolchain") != "$LEAN_TOOLCHAIN_EXPECTED" ]]; then
    echo "Lean toolchain mismatch" >&2; return 1
  fi
  if [[ $(git -C "$PROJECT_ROOT/.lake/packages/mathlib" rev-parse HEAD) != "$MATHLIB_COMMIT_EXPECTED" ]]; then
    echo "Mathlib commit mismatch" >&2; return 1
  fi
  export ELAN_TOOLCHAIN="$LEAN_TOOLCHAIN_EXPECTED"
}

validation_sha256() {
  shasum -a 256 "$1" | awk '{print $1}'
}

validation_fresh_workdir() {
  local label=$1
  mkdir -p "$VALIDATION_ROOT/.work/runs"
  mktemp -d "$VALIDATION_ROOT/.work/runs/${label}.XXXXXX"
}

validation_check_no_escapes() {
  local lean_path=$1 rocq_path=$2
  if rg -n '\b(sorry|axiom|unsafe)\b' "$lean_path" --glob '*.lean'; then
    echo "forbidden production proof escape" >&2
    return 1
  fi
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$rocq_path" --glob '*.v'; then
    echo "forbidden certificate proof escape" >&2
    return 1
  fi
}

validation_prepare_lean_path() {
  local work=$1
  local mathlib_path
  mathlib_path=$(cd "$PROJECT_ROOT" && lake env printenv LEAN_PATH)
  export LEAN_PATH="$work/olean:$PROJECT_ROOT:$mathlib_path"
}

validation_compile_lean_module() {
  local work=$1 module_path=$2
  mkdir -p "$work/olean/$(dirname "$module_path")"
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    -o "$work/olean/${module_path}.olean" \
    "$PROJECT_ROOT/${module_path}.lean"
}

validation_compile_official_source() {
  local work=$1 source_file=$2 expected_hash=$3
  mkdir -p "$work/source/$(dirname "$source_file")"
  cp "$SOURCE_ROOT/$source_file" "$work/source/$source_file"
  [[ $(validation_sha256 "$work/source/$source_file") == "$expected_hash" ]]
  (
    cd "$work/source"
    opam exec --switch="$ROCQ_SWITCH" -- rocq c \
      -R "$work/source" prosa "$source_file"
  )
}

validation_rocq_compile() {
  local work=$1 source_file=$2
  opam exec --switch="$ROCQ_SWITCH" -- rocq c \
    -R "$work/source" prosa \
    -Q "$IMPORTER_ROOT/src" LeanImport -I "$IMPORTER_ROOT/src" \
    -Q "$work/imported" FoundationImported \
    -Q "$work/certificates" FoundationCertificates \
    "$source_file"
}

validation_verify_tool_hashes() {
  if [[ $(validation_sha256 "$EXPORTER_ROOT/.lake/build/bin/lean4export") != \
      c20dbe1f14951dbcb2b806395f171d3e91e9bb5ccc22fa5cb63bd592a767e49b ]]; then
    echo "lean4export binary hash mismatch" >&2; return 1
  fi
  if [[ $(validation_sha256 "$IMPORTER_ROOT/src/lean_import.cmxs") != \
      c3a10b84f88ff66a3fcff8e15e3c0a6a307592b45726c612fa8a95b061d97982 ]]; then
    echo "rocq-lean-import plugin hash mismatch" >&2; return 1
  fi
  if [[ $(validation_sha256 "$IMPORTER_ROOT/src/Lean.vo") != \
      0ec01795b0a3d6646fb72824262eb7888677ac3ee4cbfc665f6a68309c54fd70 ]]; then
    echo "rocq-lean-import foundation hash mismatch" >&2; return 1
  fi
}
