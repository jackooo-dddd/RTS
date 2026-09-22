#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
exec "$script_dir/run_incremental_validation.sh" "${1:-finalize}" \
  --name behavior_schedule \
  --config "$script_dir/../tooling/behavior_schedule_incremental_descriptor.json" \
  --hooks "$script_dir/../tooling/behavior_schedule_incremental_hooks.sh"
