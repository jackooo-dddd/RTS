#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
exec "$script_dir/run_incremental_validation.sh" "${1:-finalize}" \
  --name model_processor_supply \
  --config "$script_dir/../tooling/model_processor_supply_incremental_descriptor.json" \
  --hooks "$script_dir/../tooling/model_processor_supply_incremental_hooks.sh"
