#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
exporter_src=${LEAN4EXPORT_SRC:-/private/tmp/lean4export}
toolchain=${LEAN_TOOLCHAIN:-leanprover/lean4:v4.33.1}
work=$(mktemp -d "$validation_root/.work/cache_invalidation.XXXXXX")
log="$validation_root/reports/logs/experiment7/cache_invalidation_test.log"
mkdir -p "$(dirname "$log")" "$work/source" "$work/build0" "$work/build1"

exporter="$exporter_src/.lake/build/bin/lean4export"
[[ -x "$exporter" ]] || ELAN_TOOLCHAIN="$toolchain" lake -d "$exporter_src" build lean4export

build_and_export() {
  local variant=$1 build_dir=$2 artifact=$3
  cp "$validation_root/lean_fixtures/$variant/CacheProbe.lean" "$work/source/CacheProbe.lean"
  ELAN_TOOLCHAIN="$toolchain" lean -o "$build_dir/CacheProbe.olean" \
    "$work/source/CacheProbe.lean"
  ELAN_TOOLCHAIN="$toolchain" LEAN_PATH="$build_dir" \
    "$exporter" CacheProbe -- CacheProbe.value > "$artifact"
}

build_and_export cache_probe_v0 "$work/build0" "$work/cache_probe_v0.out"
build_and_export cache_probe_v1 "$work/build1" "$work/cache_probe_v1.out"
hash0=$(shasum -a 256 "$work/cache_probe_v0.out" | awk '{print $1}')
hash1=$(shasum -a 256 "$work/cache_probe_v1.out" | awk '{print $1}')

{
  echo "toolchain=$toolchain"
  echo "work=$work"
  echo "v0_hash=$hash0"
  echo "v1_hash=$hash1"
} > "$log"

if [[ "$hash0" == "$hash1" ]]; then
  echo "cache invalidation failure: source changed but artifact hash did not" >&2
  exit 1
fi
result="clean rebuild cache invalidation: PASS ($hash0 != $hash1)"
echo "$result" >> "$log"
echo "$result"
