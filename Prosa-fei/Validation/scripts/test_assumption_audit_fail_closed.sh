#!/usr/bin/env bash
set -euo pipefail

validation_root=$(cd "$(dirname "$0")/.." && pwd)
classifier="$validation_root/scripts/classify_assumptions.py"
config="$validation_root/mapping/experiment11_fail_closed_audit.yaml"
work=$(mktemp -d "${TMPDIR:-/tmp}/assumption-fail-closed.XXXXXX")
trap 'rm -rf "$work"' EXIT

run_rejected() {
  local label=$1 log=$2
  local output="$work/$label.json"
  if python3 "$classifier" --config "$config" --log "$log" \
      --output "$output" > "$work/$label.stdout" 2>&1; then
    echo "$label was incorrectly accepted" >&2
    exit 1
  fi
  python3 - "$output" <<'PY'
import json, sys
item = json.load(open(sys.argv[1]))["certificates"]["probe"]
assert item["status"] == "AUDIT_MISSING", item
PY
}

: > "$work/missing.log"
printf 'AUDIT_BEGIN probe\nClosed under the global context\n' > "$work/truncated.log"
run_rejected missing "$work/missing.log"
run_rejected truncated "$work/truncated.log"

echo "missing assumption log: REJECTED_FAIL_CLOSED"
echo "truncated assumption log: REJECTED_FAIL_CLOSED"
