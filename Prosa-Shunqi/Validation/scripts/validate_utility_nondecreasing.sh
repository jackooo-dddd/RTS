#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
exec "$script_dir/run_incremental_validation.sh" "${1:-check}" \
  --name nondecreasing \
  --config "$script_dir/../tooling/nondecreasing_incremental_descriptor.json" \
  --hooks "$script_dir/../tooling/nondecreasing_incremental_hooks.sh"
