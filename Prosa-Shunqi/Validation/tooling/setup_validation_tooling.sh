#!/usr/bin/env bash
set -euo pipefail

tooling_dir=$(cd "$(dirname "$0")" && pwd)
validation_root=$(cd "$tooling_dir/.." && pwd)
work_root="$validation_root/.work/tooling"
exporter="$work_root/lean4export"
importer="$work_root/rocq-lean-import"
exporter_url=https://github.com/leanprover/lean4export.git
importer_url=https://github.com/rocq-community/rocq-lean-import.git
exporter_commit=c9f8373f8a37a65c0ed9bfd20480a3d7481a163e
importer_commit=546979bfd55b94288abfb72583a534b0136d282d
exporter_patch="$tooling_dir/patches/lean4export.patch"
importer_patch="$tooling_dir/patches/rocq-lean-import.patch"
expected_exporter_patch=4df7fff23895b6efbbf7e3255330e9cab4a3833b02c48a3e8edd11c590fcdbc4
expected_importer_patch=0b3f5ad7903d43ee211f77d92a814ab799d0392bd6848d6eec5906a16b5de3f4
expected_exporter_diff=$expected_exporter_patch
expected_importer_diff=$expected_importer_patch
expected_exporter_status=2be73180d81e431f05e5311437ba98e26e0440bf00f75e2adad0ec46c1bb92e2
expected_importer_status=36e27329d0e78477933bec8f1889b14d6fb3e75ca96656227f9483ed03fd8104
rocq_switch=${IMPORT_OPAM_SWITCH:-rocq93rc1}

sha256() { shasum -a 256 "$1" | awk '{print $1}'; }
stream_sha256() { shasum -a 256 | awk '{print $1}'; }

[[ $(sha256 "$exporter_patch") == "$expected_exporter_patch" ]]
[[ $(sha256 "$importer_patch") == "$expected_importer_patch" ]]
mkdir -p "$work_root"

prepare_checkout() {
  local url=$1 target=$2 commit=$3 patch=$4 preserve_original=${5:-0}
  if [[ ! -e "$target/.git" ]]; then
    if [[ -e "$target" ]]; then
      echo "tool target exists but is not a Git checkout: $target" >&2
      exit 1
    fi
    git clone "$url" "$target"
    git -C "$target" checkout --detach "$commit"
    if [[ "$preserve_original" == 1 ]]; then
      cp "$target/Export.lean" "$target/Export.lean.orig"
    fi
    git -C "$target" apply "$patch"
  fi
  [[ $(git -C "$target" rev-parse HEAD) == "$commit" ]] || {
    echo "tool base commit mismatch: $target" >&2
    exit 1
  }
}

prepare_checkout "$exporter_url" "$exporter" "$exporter_commit" "$exporter_patch" 1
prepare_checkout "$importer_url" "$importer" "$importer_commit" "$importer_patch" 0

[[ $(git -C "$exporter" diff | stream_sha256) == "$expected_exporter_diff" ]]
[[ $(git -C "$importer" diff | stream_sha256) == "$expected_importer_diff" ]]
[[ $(git -C "$exporter" status --porcelain | stream_sha256) == "$expected_exporter_status" ]]
[[ $(git -C "$importer" status --porcelain | stream_sha256) == "$expected_importer_status" ]]

ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1 lake -d "$exporter" build lean4export
opam exec --switch="$rocq_switch" -- make -C "$importer" -j2

cat <<EOF
LEAN4EXPORT_SRC=$exporter
ROCQLI_SRC=$importer
LEAN4EXPORT_BINARY_SHA256=$(sha256 "$exporter/.lake/build/bin/lean4export")
ROCQLI_PLUGIN_SHA256=$(sha256 "$importer/src/lean_import.cmxs")
ROCQLI_FOUNDATION_SHA256=$(sha256 "$importer/src/Lean.vo")
EOF
