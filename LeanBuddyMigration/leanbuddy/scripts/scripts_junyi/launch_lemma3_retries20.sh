#!/usr/bin/env bash
# Launch two NEW independent parallel prosabuddy workers for 2005-ECRTS-Lemma3
# with max-retries=20. Does NOT touch existing run1/run2 workers.
#
# Usage: ./scripts/launch_lemma3_retries20.sh
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$SCRIPT_DIR/opencode_runner_config.sh"
opencode_config_load
opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

PYTHON_BIN="${PYTHON_BIN:-$(command -v python3)}"
SERIAL_RUNNER="${OPENCODE_SERIAL_RUNNER:-$SCRIPT_DIR/run_casestudy_our_minprosa.py}"
OPENCODE_BIN="${OPENCODE_BIN:-$SCRIPT_DIR/opencode_our_local.sh}"
CASES_DIR="${OPENCODE_CASESTUDY_DIR:-/home/junyi/dataset/Case_Study}"
FULL_PROSA_SOURCE_DIR="${OPENCODE_FULL_PROSA_SOURCE_DIR:-/home/junyi/prosabuddy/prosaworkspace}"
RESULTS_ROOT="${OPENCODE_RESULTS_ROOT:-/home/junyi/results_rebuttal}"
CASE_NAME="2005-ECRTS-Lemma3"
MAX_TOTAL_TOKENS="${OPENCODE_MAX_TOTAL_TOKENS:-80000000}"
MAX_RETRIES=20
RUN_TIMEOUT_SECONDS="${OPENCODE_RUN_TIMEOUT_SECONDS:-43200}"
LAUNCH_STAGGER_SECONDS="${OPENCODE_LAUNCH_STAGGER_SECONDS:-10}"
AUTH_SOURCE="${OPENCODE_AUTH_SOURCE:-${XDG_DATA_HOME:-$HOME/.local/share}/opencode/auth.json}"
MODEL_STATE_SOURCE="${OPENCODE_MODEL_STATE_SOURCE:-${XDG_STATE_HOME:-$HOME/.local/state}/opencode/model.json}"

# New worker result prefixes (distinct from existing run1/run2).
declare -a WORKER_SPECS=(
  "new1|our_casestudy_fullprosa_rebuttal_new1"
  "new2|our_casestudy_fullprosa_rebuttal_new2"
)

for f in "$SERIAL_RUNNER" "$OPENCODE_BIN" "$AUTH_SOURCE" "$MODEL_STATE_SOURCE"; do
  if [[ ! -e "$f" ]]; then
    echo "ERROR: required file not found: $f" >&2
    exit 1
  fi
done
if [[ ! -d "$CASES_DIR/$CASE_NAME" ]]; then
  echo "ERROR: casestudy not found: $CASES_DIR/$CASE_NAME" >&2
  exit 1
fi
if [[ ! -d "$FULL_PROSA_SOURCE_DIR" ]]; then
  echo "ERROR: full Prosa source not found: $FULL_PROSA_SOURCE_DIR" >&2
  exit 1
fi

if [[ "${1:-}" == "--check" ]]; then
  echo "preflight=ok"
  echo "case=$CASES_DIR/$CASE_NAME"
  echo "parallel=${#WORKER_SPECS[@]}"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  exit 0
fi
if [[ $# -ne 0 ]]; then
  echo "Usage: $(basename "$0") [--check]" >&2
  exit 2
fi

STAMP="$(date +%Y%m%d_%H%M%S)"
ACCOUNTS_ROOT="$RESULTS_ROOT/accounts_lemma3_retries20_${STAMP}"
LOG_DIR="$RESULTS_ROOT/nohup"
mkdir -p "$ACCOUNTS_ROOT" "$LOG_DIR"

declare -a WORKER_PIDS=()
declare -a WORKER_IDS=()

terminate_workers() {
  local pid
  for pid in "${WORKER_PIDS[@]:-}"; do
    if [[ -n "$pid" ]] && kill -0 "$pid" 2>/dev/null; then
      kill "$pid" 2>/dev/null || true
    fi
  done
  for pid in "${WORKER_PIDS[@]:-}"; do
    if [[ -n "$pid" ]]; then
      wait "$pid" 2>/dev/null || true
    fi
  done
}

trap 'terminate_workers; exit 130' INT TERM

echo "=== Launching two NEW parallel prosabuddy workers ==="
echo "Case:       $CASE_NAME"
echo "Max retries:$MAX_RETRIES  (was 8, now 20)"
echo "Max tokens: $MAX_TOTAL_TOKENS"
echo "Timeout:    ${RUN_TIMEOUT_SECONDS}s"
echo "Results:    $RESULTS_ROOT"
echo "Accounts:   $ACCOUNTS_ROOT"
echo "Existing run1/run2 workers are left untouched."
echo ""

for spec in "${WORKER_SPECS[@]}"; do
  worker_id="${spec%%|*}"
  result_prefix="${spec##*|}"
  WORKER_ROOT="$ACCOUNTS_ROOT/worker_${worker_id}"
  WORKER_DATA_HOME="$WORKER_ROOT/data"
  WORKER_STATE_HOME="$WORKER_ROOT/state"
  WORKER_LOG="$LOG_DIR/our_lemma3_new_${worker_id}_${STAMP}.log"

  mkdir -p "$WORKER_DATA_HOME/opencode" "$WORKER_STATE_HOME/opencode"
  install -m 600 "$AUTH_SOURCE" "$WORKER_DATA_HOME/opencode/auth.json"
  install -m 600 "$MODEL_STATE_SOURCE" "$WORKER_STATE_HOME/opencode/model.json"

  echo "[launch] worker=$worker_id result_prefix=$result_prefix log=$WORKER_LOG"
  env -u OPENCODE_MODEL \
      XDG_DATA_HOME="$WORKER_DATA_HOME" \
      XDG_STATE_HOME="$WORKER_STATE_HOME" \
      OPENCODE_RUN_NOHUP=0 \
      OPENCODE_RESULTS_ROOT="$RESULTS_ROOT" \
      OPENCODE_RESULT_PREFIX="$result_prefix" \
      "$PYTHON_BIN" "$SERIAL_RUNNER" \
          --cases-dir "$CASES_DIR" \
          --run-timeout-seconds "$RUN_TIMEOUT_SECONDS" \
          --max-total-tokens "$MAX_TOTAL_TOKENS" \
          --max-retries "$MAX_RETRIES" \
          --opencode-bin "$OPENCODE_BIN" \
          --stage-full-casestudy-workspace \
          --full-prosa \
          --full-prosa-source-dir "$FULL_PROSA_SOURCE_DIR" \
          --segmented-proof-workflow \
          --skill \
          --trace-requests \
          "$CASE_NAME" >"$WORKER_LOG" 2>&1 &

  worker_pid="$!"
  WORKER_PIDS+=("$worker_pid")
  WORKER_IDS+=("$worker_id")
  echo "worker_${worker_id}_pid=$worker_pid"
  echo "worker_${worker_id}_pid=$worker_pid" >>"$ACCOUNTS_ROOT/pids.txt"
  if [[ "$LAUNCH_STAGGER_SECONDS" -gt 0 ]]; then
    sleep "$LAUNCH_STAGGER_SECONDS"
  fi
done

echo ""
echo "Both new workers launched in background. Logs:"
for spec in "${WORKER_SPECS[@]}"; do
  worker_id="${spec%%|*}"
  echo "  worker_${worker_id}: $LOG_DIR/our_lemma3_new_${worker_id}_${STAMP}.log"
done
echo "Accounts root: $ACCOUNTS_ROOT"

overall_status=0
for worker_offset in "${!WORKER_PIDS[@]}"; do
  set +e
  wait "${WORKER_PIDS[$worker_offset]}"
  worker_status="$?"
  set -e
  worker_id="${WORKER_IDS[$worker_offset]}"
  echo "worker_${worker_id}_status=$worker_status" >>"$ACCOUNTS_ROOT/status.txt"
  if [[ "$worker_status" -ne 0 ]]; then
    overall_status=1
  fi
done

echo "finished_at=$(date --iso-8601=seconds)" >>"$ACCOUNTS_ROOT/status.txt"
echo "overall_status=$overall_status" >>"$ACCOUNTS_ROOT/status.txt"
exit "$overall_status"
