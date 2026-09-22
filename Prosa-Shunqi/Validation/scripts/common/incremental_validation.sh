#!/usr/bin/env bash

# Shared prepare/check/finalize bookkeeping.  Source this after
# validation_common.sh; callers remain responsible for executing the actual
# Lean/Rocq commands and for the semantic acceptance policy.

validation_incremental_state_tool() {
  printf '%s\n' "$VALIDATION_ROOT/scripts/incremental_validation_state.py"
}

validation_now_ns() {
  python3 -c 'import time; print(time.time_ns())'
}

validation_stage_fingerprint() {
  python3 - "$@" <<'PY'
import hashlib, json, sys
from pathlib import Path

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

items = {}
for item in sys.argv[1:]:
    name, path = item.split('=', 1)
    p = Path(path)
    if not p.is_file() or p.stat().st_size == 0:
        raise SystemExit('stage fingerprint input absent or empty: ' + path)
    items[name] = sha(p)
print(hashlib.sha256(json.dumps(items, sort_keys=True).encode()).hexdigest())
PY
}

validation_record_stage() {
  local events=$1 stage=$2 mode=$3 executed=$4 start_ns=$5 end_ns=$6 fingerprint=$7
  shift 7
  local tool
  tool=$(validation_incremental_state_tool)
  local args=(
    record --output "$events" --stage "$stage" --mode "$mode"
    --executed "$executed" --status PASS --start-ns "$start_ns"
    --end-ns "$end_ns" --input-fingerprint "$fingerprint"
  )
  local output
  for output in "$@"; do args+=(--output-file "$output"); done
  python3 "$tool" "${args[@]}"
}

validation_record_failed_stage() {
  local events=$1 stage=$2 start_ns=$3 end_ns=$4 fingerprint=$5 reason=$6
  python3 "$(validation_incremental_state_tool)" record \
    --output "$events" --stage "$stage" --mode FAILED --executed true \
    --status FAIL --start-ns "$start_ns" --end-ns "$end_ns" \
    --input-fingerprint "$fingerprint" --failure-reason "$reason"
}

validation_finish_incremental_run() {
  local events=$1 snapshot_id=$2 run_mode=$3 output=$4
  python3 "$(validation_incremental_state_tool)" finish-run \
    --events "$events" --snapshot-id "$snapshot_id" \
    --run-mode "$run_mode" --output "$output"
}
