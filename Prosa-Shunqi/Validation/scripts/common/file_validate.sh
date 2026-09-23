#!/usr/bin/env bash

# Source after validation_common.sh. On stale producer evidence, callers may
# build the complete dependency closure. Corrupt artifacts fail closed.
validation_file_dependencies() {
  local producer_name=$1 producer_manifest=$2 producer_status=$3
  shift 3
  local producer_snapshot producer_root result
  producer_snapshot=$(python3 - "$producer_manifest" <<'PY'
import json, sys
print(json.load(open(sys.argv[1]))["snapshot_id"])
PY
)
  producer_root="$VALIDATION_ROOT/.work/incremental/$producer_name/$producer_snapshot"
  local args=(materialize --project "$PROJECT_ROOT" --producer "$producer_root"
    --accepted-manifest "$producer_manifest" --accepted-status "$producer_status"
    --destination "$VALIDATION_PREPARED/olean"
    --evidence "$VALIDATION_PREPARED/lean_dependency_reuse.json")
  local module
  for module in "$@"; do args+=(--module "$module"); done
  set +e
  python3 "$VALIDATION_ROOT/scripts/file_validate_lean_dependencies.py" "${args[@]}" \
    > "$VALIDATION_RUN_LOG/dependency_reuse.log" 2>&1
  result=$?
  set -e
  if [[ $result -eq 0 ]]; then
    return 0
  fi
  if [[ $result -eq 2 ]]; then
    echo "producer stale; rebuilding dependency closure" >&2
    return 2
  fi
  cat "$VALIDATION_RUN_LOG/dependency_reuse.log" >&2
  return 3
}

validation_seal_lean_modules() {
  local args=(seal --project "$PROJECT_ROOT" --olean "$VALIDATION_PREPARED/olean"
    --mode "$1" --output "$VALIDATION_PREPARED/lean_source_build_manifest.json")
  if [[ -s "$VALIDATION_PREPARED/lean_dependency_reuse.json" ]]; then
    args+=(--reuse-evidence "$VALIDATION_PREPARED/lean_dependency_reuse.json")
  fi
  python3 "$VALIDATION_ROOT/scripts/file_validate_lean_dependencies.py" "${args[@]}"
}
