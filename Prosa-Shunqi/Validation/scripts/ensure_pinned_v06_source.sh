#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
validation_root=$(cd "$script_dir/.." && pwd)
source_url=${PROSA_V06_UPSTREAM_URL:-https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs.git}
expected_commit=414e66760333eaa4ef78c685bcf53291c527a548
expected_tree=7d7e94c731f7eefde4ca738310d4cafdd7bebdf0
target=${PROSA_V06_SOURCE_ROOT:-"$validation_root/.work/prosa-v06-414e667"}

mkdir -p "$validation_root/.work"

if [[ ! -e "$target/.git" ]]; then
  if [[ -e "$target" ]]; then
    echo "source target exists but is not a Git checkout: $target" >&2
    exit 1
  fi
  git clone --filter=blob:none --no-checkout "$source_url" "$target"
  git -C "$target" checkout --detach "$expected_commit"
fi

actual_commit=$(git -C "$target" rev-parse HEAD)
actual_tree=$(git -C "$target" rev-parse HEAD^{tree})
actual_remote=$(git -C "$target" remote get-url origin)

[[ "$actual_commit" == "$expected_commit" ]] || {
  echo "pinned source commit mismatch: expected $expected_commit, got $actual_commit" >&2
  exit 1
}
[[ "$actual_tree" == "$expected_tree" ]] || {
  echo "pinned source tree mismatch: expected $expected_tree, got $actual_tree" >&2
  exit 1
}
[[ "$actual_remote" == "$source_url" ]] || {
  echo "pinned source remote mismatch: expected $source_url, got $actual_remote" >&2
  exit 1
}
[[ -z $(git -C "$target" status --porcelain --untracked-files=all) ]] || {
  echo "pinned source checkout is not clean: $target" >&2
  git -C "$target" status --short >&2
  exit 1
}

printf '%s\n' "$target"

