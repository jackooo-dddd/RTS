#!/usr/bin/env bash
set -euo pipefail

# Compatibility entry point.  List validation is now explicitly split into:
#   prepare_utility_list_batch.sh  -- content-addressed Lean/export/import
#   check_utility_list_batch.sh    -- certificate-only development checks
#   finalize_utility_list_batch.sh -- full batch regression and publication
script_dir=$(cd "$(dirname "$0")" && pwd)
exec "$script_dir/finalize_utility_list_batch.sh" "$@"
