#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$SCRIPT_DIR/opencode_runner_config.sh"
opencode_config_load
opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

PYTHON_BIN="${PYTHON_BIN:-/usr/bin/python3}"
RUNNER="${OPENCODE_SERIAL_RUNNER:-$SCRIPT_DIR/run_casestudy_our_minprosa.py}"
OPENCODE_BIN="${OPENCODE_BIN:-$SCRIPT_DIR/opencode_our_local.sh}"
CASES_DIR="${OPENCODE_CASESTUDY_DIR:-/home/junyi/dataset/Case_Study}"
FULL_PROSA_SOURCE_DIR="${OPENCODE_FULL_PROSA_SOURCE_DIR:-/home/junyi/prosabuddy/prosaworkspace}"
RESULTS_ROOT="${OPENCODE_RESULTS_ROOT:-/home/junyi/results_rebuttal}"
AUTH_SOURCE="${OPENCODE_AUTH_SOURCE:-/home/junyi/.local/share/opencode/auth.json}"
ROCQ_BIN_DIR="${OPENCODE_ROCQ_BIN_DIR:-/home/junyi/.opam/rocq-4.14/bin}"
BUN_BIN="${BUN_BIN:-/home/junyi/.bun/bin/bun}"
WORKER_PATH="$ROCQ_BIN_DIR:/home/junyi/.bun/bin:/home/junyi/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

MODEL="${OPENCODE_DEEPSEEK_MODEL:-deepseek/deepseek-v4-flash}"
MAX_TOTAL_TOKENS="${DEEPSEEK_2X_MAX_TOTAL_TOKENS:-${DEEPSEEK_RTSS_METHOD1_2X_MAX_TOTAL_TOKENS:-20000000}}"
MAX_RETRIES="${DEEPSEEK_2X_MAX_RETRIES:-${DEEPSEEK_RTSS_METHOD1_2X_MAX_RETRIES:-20}}"
RUN_TIMEOUT_SECONDS="${OPENCODE_RUN_TIMEOUT_SECONDS:-43200}"
MODEL_RESPONSE_TIMEOUT_SECONDS="${OPENCODE_MODEL_RESPONSE_TIMEOUT_SECONDS:-600}"
LAUNCH_STAGGER_SECONDS="${OPENCODE_LAUNCH_STAGGER_SECONDS:-2}"
SUPERVISOR_TAG="${DEEPSEEK_2X_SUPERVISOR_TAG:-deepseek_2009_rtss_method1_2x}"
CASE_NAME="${DEEPSEEK_2X_CASE_NAME:-2009-RTSS-Method1}"
WORKER_BASE="${DEEPSEEK_2X_WORKER_BASE:-deepseek_2009_rtss_method1}"

WORKER_NAMES=(
  "${WORKER_BASE}_run1"
  "${WORKER_BASE}_run2"
)

check_prerequisites() {
  local required resolved
  for required in \
    "$PYTHON_BIN" "$RUNNER" "$OPENCODE_BIN" "$AUTH_SOURCE" "$BUN_BIN" \
    "$ROCQ_BIN_DIR/coqc" "$ROCQ_BIN_DIR/coqtop" "$ROCQ_BIN_DIR/rocq" \
    "$FULL_PROSA_SOURCE_DIR" "$CASES_DIR/$CASE_NAME"; do
    if [[ ! -e "$required" ]]; then
      echo "ERROR: required path not found: $required" >&2
      return 1
    fi
  done
  for required in "$PYTHON_BIN" "$OPENCODE_BIN" "$BUN_BIN" "$ROCQ_BIN_DIR/coqc" "$ROCQ_BIN_DIR/coqtop" "$ROCQ_BIN_DIR/rocq"; do
    if [[ ! -x "$required" ]]; then
      echo "ERROR: executable path is not executable: $required" >&2
      return 1
    fi
  done
  resolved="$(PATH="$WORKER_PATH" command -v coqc || true)"
  if [[ "$resolved" != "$ROCQ_BIN_DIR/coqc" ]]; then
    echo "ERROR: coqc PATH mismatch: expected $ROCQ_BIN_DIR/coqc, got ${resolved:-<not found>}" >&2
    return 1
  fi
  resolved="$(PATH="$WORKER_PATH" command -v coqtop || true)"
  if [[ "$resolved" != "$ROCQ_BIN_DIR/coqtop" ]]; then
    echo "ERROR: coqtop PATH mismatch: expected $ROCQ_BIN_DIR/coqtop, got ${resolved:-<not found>}" >&2
    return 1
  fi
  resolved="$(PATH="$WORKER_PATH" command -v rocq || true)"
  if [[ "$resolved" != "$ROCQ_BIN_DIR/rocq" ]]; then
    echo "ERROR: rocq PATH mismatch: expected $ROCQ_BIN_DIR/rocq, got ${resolved:-<not found>}" >&2
    return 1
  fi
  PATH="$WORKER_PATH" "$ROCQ_BIN_DIR/coqc" --version >/dev/null
  if ! grep -q '"deepseek"' "$AUTH_SOURCE"; then
    echo "ERROR: DeepSeek authentication is absent from $AUTH_SOURCE" >&2
    return 1
  fi
}

check_prerequisites

if [[ "${1:-}" == "--check" && $# -eq 1 ]]; then
  echo "preflight=ok"
  echo "workers=${#WORKER_NAMES[@]}"
  echo "model=$MODEL"
  echo "case=$CASE_NAME"
  echo "coqc=$ROCQ_BIN_DIR/coqc"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  echo "run_timeout_seconds=$RUN_TIMEOUT_SECONDS"
  exit 0
fi
if [[ $# -ne 0 ]]; then
  echo "Usage: $(basename "$0") [--check]" >&2
  exit 2
fi

STAMP="$(date +%Y%m%d_%H%M%S)"
SUPERVISOR_DIR="$RESULTS_ROOT/supervisor/${SUPERVISOR_TAG}_$STAMP"
mkdir -p "$SUPERVISOR_DIR"
printf '%s\n' "$SUPERVISOR_DIR" >"$RESULTS_ROOT/supervisor/${SUPERVISOR_TAG}_latest.txt"

declare -a WORKER_PIDS=()
declare -a WORKER_IDS=()

terminate_worker_group() {
  local pid="$1"
  [[ -n "$pid" ]] || return 0
  if kill -0 -- "-$pid" 2>/dev/null; then
    kill -TERM -- "-$pid" 2>/dev/null || true
    for _ in {1..50}; do
      kill -0 -- "-$pid" 2>/dev/null || return 0
      sleep 0.1
    done
    kill -KILL -- "-$pid" 2>/dev/null || true
  fi
}

terminate_workers() {
  local pid
  for pid in "${WORKER_PIDS[@]:-}"; do
    terminate_worker_group "$pid"
  done
}

supervisor_exit_status=0
on_supervisor_exit() {
  supervisor_exit_status="$?"
  trap - EXIT INT TERM HUP
  terminate_workers
  exit "$supervisor_exit_status"
}
trap on_supervisor_exit EXIT INT TERM HUP

{
  echo "workers=${#WORKER_NAMES[@]}"
  echo "model=$MODEL"
  echo "case=$CASE_NAME"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  echo "run_timeout_seconds=$RUN_TIMEOUT_SECONDS"
  echo "model_response_timeout_seconds=$MODEL_RESPONSE_TIMEOUT_SECONDS"
  echo "coqc=$ROCQ_BIN_DIR/coqc"
  echo "started_at=$(date --iso-8601=seconds)"
  for worker_offset in "${!WORKER_NAMES[@]}"; do
    echo "worker_$((worker_offset + 1))=${WORKER_NAMES[$worker_offset]}|$CASE_NAME|$MODEL"
  done
} >"$SUPERVISOR_DIR/config.txt"

echo "supervisor_dir=$SUPERVISOR_DIR"
for worker_offset in "${!WORKER_NAMES[@]}"; do
  worker_name="${WORKER_NAMES[$worker_offset]}"
  worker_root="$SUPERVISOR_DIR/$worker_name"
  worker_log="$SUPERVISOR_DIR/$worker_name.log"
  result_prefix="our_casestudy_fullprosa_${worker_name}"

  mkdir -p "$worker_root/data/opencode" "$worker_root/state/opencode" "$worker_root/cache"
  install -m 600 "$AUTH_SOURCE" "$worker_root/data/opencode/auth.json"

  echo "[launch] worker=$worker_name case=$CASE_NAME model=$MODEL log=$worker_log"
  setsid env -u OPENCODE_MODEL -u OPENCODE_VARIANT \
    "PATH=$WORKER_PATH" \
    "BUN_BIN=$BUN_BIN" \
    "XDG_DATA_HOME=$worker_root/data" \
    "XDG_STATE_HOME=$worker_root/state" \
    "XDG_CACHE_HOME=$worker_root/cache" \
    OPENCODE_RUN_NOHUP=0 \
    PYTHONUNBUFFERED=1 \
    "OPENCODE_RESULTS_ROOT=$RESULTS_ROOT" \
    "OPENCODE_RESULT_PREFIX=$result_prefix" \
    "$PYTHON_BIN" "$RUNNER" \
      --model "$MODEL" \
      --cases-dir "$CASES_DIR" \
      --run-timeout-seconds "$RUN_TIMEOUT_SECONDS" \
      --model-response-timeout-seconds "$MODEL_RESPONSE_TIMEOUT_SECONDS" \
      --max-total-tokens "$MAX_TOTAL_TOKENS" \
      --max-retries "$MAX_RETRIES" \
      --opencode-bin "$OPENCODE_BIN" \
      --stage-full-casestudy-workspace \
      --full-prosa \
      --full-prosa-source-dir "$FULL_PROSA_SOURCE_DIR" \
      --segmented-proof-workflow \
      --skill \
      --trace-requests \
      "$CASE_NAME" >"$worker_log" 2>&1 &

  worker_pid="$!"
  WORKER_PIDS+=("$worker_pid")
  WORKER_IDS+=("$worker_name")
  printf '%s=%s\n' "$worker_name" "$worker_pid" >>"$SUPERVISOR_DIR/pids.txt"
  if [[ "$worker_offset" -lt $((${#WORKER_NAMES[@]} - 1)) ]] && [[ "$LAUNCH_STAGGER_SECONDS" -gt 0 ]]; then
    sleep "$LAUNCH_STAGGER_SECONDS"
  fi
done

overall_status=0
for worker_offset in "${!WORKER_PIDS[@]}"; do
  set +e
  wait "${WORKER_PIDS[$worker_offset]}"
  worker_status="$?"
  set -e
  terminate_worker_group "${WORKER_PIDS[$worker_offset]}"
  printf '%s=%s\n' "${WORKER_IDS[$worker_offset]}" "$worker_status" >>"$SUPERVISOR_DIR/status.txt"
  if [[ "$worker_status" -ne 0 ]]; then
    overall_status=1
  fi
done

echo "finished_at=$(date --iso-8601=seconds)" >>"$SUPERVISOR_DIR/status.txt"
echo "overall_status=$overall_status" >>"$SUPERVISOR_DIR/status.txt"
trap - EXIT INT TERM HUP
exit "$overall_status"
