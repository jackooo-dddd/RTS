#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$SCRIPT_DIR/opencode_runner_config.sh"
opencode_config_load

PYTHON_BIN="${PYTHON_BIN:-/usr/bin/python3}"
SERIAL_RUNNER="${OPENCODE_SERIAL_RUNNER:-$SCRIPT_DIR/run_casestudy_our_minprosa.py}"
OPENCODE_BIN="${OPENCODE_BIN:-$SCRIPT_DIR/opencode_our_local.sh}"
CASES_DIR="${OPENCODE_CASESTUDY_DIR:-/home/junyi/dataset/Case_Study}"
FULL_PROSA_SOURCE_DIR="${OPENCODE_FULL_PROSA_SOURCE_DIR:-/home/junyi/prosabuddy/prosaworkspace}"
RESULTS_ROOT="${OPENCODE_RESULTS_ROOT:-/home/junyi/results_rebuttal}"
AUTH_SOURCE="${OPENCODE_AUTH_SOURCE:-/home/junyi/.local/share/opencode/auth.json}"
ROCQ_BIN_DIR="${OPENCODE_ROCQ_BIN_DIR:-/home/junyi/.opam/rocq-4.14/bin}"
BUN_BIN="${BUN_BIN:-/home/junyi/.bun/bin/bun}"
# Do not inherit the sparse and installation-dependent PATH supplied by cron.
# This exact PATH is passed unchanged through Python, Bun, Prosabuddy, and all
# checkpoint/coq_session/proof-plan audit subprocesses.
WORKER_PATH="${OPENCODE_WORKER_PATH:-$ROCQ_BIN_DIR:/home/junyi/.bun/bin:/home/junyi/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin}"

CASE_NAME="2005-ECRTS-Theorem6"
MODEL="deepseek/deepseek-v4-flash"
PARALLEL=3
MAX_TOTAL_TOKENS=80000000
MAX_RETRIES=20
RUN_TIMEOUT_SECONDS="${OPENCODE_RUN_TIMEOUT_SECONDS:-43200}"
MODEL_RESPONSE_TIMEOUT_SECONDS="${OPENCODE_MODEL_RESPONSE_TIMEOUT_SECONDS:-600}"
LAUNCH_STAGGER_SECONDS="${OPENCODE_LAUNCH_STAGGER_SECONDS:-2}"

EXPECTED_LOCAL_DATE="2026-08-12"
EXPECTED_TIMEZONE="Asia/Hong_Kong"
SCHEDULED_LOCAL_TIME="04:00:00"
SCHEDULE_ID="prosabuddy-theorem6-deepseek-v4-flash-3x-20260812-0400"
CRON_TAG="# $SCHEDULE_ID"
SCHEDULE_DIR="$RESULTS_ROOT/scheduled/$SCHEDULE_ID"
STARTED_MARKER="$SCHEDULE_DIR/started"
LOCK_FILE="$SCHEDULE_DIR/launch.lock"

check_prerequisites() {
  local required resolved_coqc resolved_coqtop resolved_rocq smoke_dir smoke_file
  for required in \
    "$PYTHON_BIN" \
    "$SERIAL_RUNNER" \
    "$OPENCODE_BIN" \
    "$AUTH_SOURCE" \
    "$BUN_BIN" \
    "$ROCQ_BIN_DIR/coqc" \
    "$ROCQ_BIN_DIR/coqtop" \
    "$ROCQ_BIN_DIR/rocq"; do
    if [[ ! -e "$required" ]]; then
      echo "ERROR: required path not found: $required" >&2
      return 1
    fi
  done
  if [[ ! -x "$PYTHON_BIN" ]]; then
    echo "ERROR: Python executable is not executable: $PYTHON_BIN" >&2
    return 1
  fi
  if [[ ! -x "$OPENCODE_BIN" ]]; then
    echo "ERROR: Prosabuddy launcher is not executable: $OPENCODE_BIN" >&2
    return 1
  fi
  if [[ ! -x "$BUN_BIN" ]]; then
    echo "ERROR: Bun executable is not executable: $BUN_BIN" >&2
    return 1
  fi
  for required in "$ROCQ_BIN_DIR/coqc" "$ROCQ_BIN_DIR/coqtop" "$ROCQ_BIN_DIR/rocq"; do
    if [[ ! -x "$required" ]]; then
      echo "ERROR: Rocq tool is not executable: $required" >&2
      return 1
    fi
  done
  resolved_coqc="$(PATH="$WORKER_PATH" command -v coqc || true)"
  resolved_coqtop="$(PATH="$WORKER_PATH" command -v coqtop || true)"
  resolved_rocq="$(PATH="$WORKER_PATH" command -v rocq || true)"
  if [[ "$resolved_coqc" != "$ROCQ_BIN_DIR/coqc" ]]; then
    echo "ERROR: worker PATH does not resolve the required coqc: expected $ROCQ_BIN_DIR/coqc, got ${resolved_coqc:-<not found>}" >&2
    return 1
  fi
  if [[ "$resolved_coqtop" != "$ROCQ_BIN_DIR/coqtop" ]]; then
    echo "ERROR: worker PATH does not resolve the required coqtop: expected $ROCQ_BIN_DIR/coqtop, got ${resolved_coqtop:-<not found>}" >&2
    return 1
  fi
  if [[ "$resolved_rocq" != "$ROCQ_BIN_DIR/rocq" ]]; then
    echo "ERROR: worker PATH does not resolve the required rocq: expected $ROCQ_BIN_DIR/rocq, got ${resolved_rocq:-<not found>}" >&2
    return 1
  fi
  if ! PATH="$WORKER_PATH" "$ROCQ_BIN_DIR/coqc" --version >/dev/null; then
    echo "ERROR: coqc --version failed: $ROCQ_BIN_DIR/coqc" >&2
    return 1
  fi
  if ! PATH="$WORKER_PATH" "$ROCQ_BIN_DIR/coqc" -where >/dev/null; then
    echo "ERROR: coqc -where failed: $ROCQ_BIN_DIR/coqc" >&2
    return 1
  fi
  if ! PATH="$WORKER_PATH" "$ROCQ_BIN_DIR/coqtop" --version >/dev/null; then
    echo "ERROR: coqtop --version failed: $ROCQ_BIN_DIR/coqtop" >&2
    return 1
  fi
  if ! PATH="$WORKER_PATH" "$ROCQ_BIN_DIR/rocq" --version >/dev/null; then
    echo "ERROR: rocq --version failed: $ROCQ_BIN_DIR/rocq" >&2
    return 1
  fi

  # Exercise both compiler entry points used by Prosabuddy.  A version check
  # alone is insufficient: proof-plan premise audits use coqtop/rocq top,
  # while checkpoints select either coqc or `rocq c` from the same PATH.
  smoke_dir="$(mktemp -d)"
  smoke_file="$smoke_dir/ProsabuddyScheduledToolchainSmoke.v"
  {
    echo 'Goal True.'
    echo '  exact I.'
    echo 'Qed.'
  } >"$smoke_file"
  if ! PATH="$WORKER_PATH" "$ROCQ_BIN_DIR/coqc" "$smoke_file" >/dev/null 2>&1; then
    rm -rf "$smoke_dir"
    echo "ERROR: coqc smoke compilation failed" >&2
    return 1
  fi
  if ! PATH="$WORKER_PATH" "$ROCQ_BIN_DIR/rocq" c "$smoke_file" >/dev/null 2>&1; then
    rm -rf "$smoke_dir"
    echo "ERROR: rocq c smoke compilation failed" >&2
    return 1
  fi
  if ! PATH="$WORKER_PATH" "$ROCQ_BIN_DIR/coqtop" -batch -quiet -l "$smoke_file" >/dev/null 2>&1; then
    rm -rf "$smoke_dir"
    echo "ERROR: coqtop smoke session failed" >&2
    return 1
  fi
  if ! PATH="$WORKER_PATH" "$ROCQ_BIN_DIR/rocq" top -batch -quiet -l "$smoke_file" >/dev/null 2>&1; then
    rm -rf "$smoke_dir"
    echo "ERROR: rocq top smoke session failed" >&2
    return 1
  fi
  rm -rf "$smoke_dir"
  if [[ ! -d "$CASES_DIR/$CASE_NAME" ]]; then
    echo "ERROR: case study not found: $CASES_DIR/$CASE_NAME" >&2
    return 1
  fi
  if [[ ! -d "$FULL_PROSA_SOURCE_DIR" ]]; then
    echo "ERROR: full Prosa source not found: $FULL_PROSA_SOURCE_DIR" >&2
    return 1
  fi
  if ! grep -q '"deepseek"' "$AUTH_SOURCE"; then
    echo "ERROR: DeepSeek authentication is absent from $AUTH_SOURCE" >&2
    return 1
  fi
  if [[ "$(date +%Z)" != "HKT" ]] && [[ "$(timedatectl show -p Timezone --value 2>/dev/null || true)" != "$EXPECTED_TIMEZONE" ]]; then
    echo "ERROR: expected timezone $EXPECTED_TIMEZONE, current timezone is $(date +%Z)" >&2
    return 1
  fi
}

remove_own_cron_entry() {
  local current next
  current="$(mktemp)"
  next="$(mktemp)"
  crontab -l >"$current" 2>/dev/null || true
  grep -Fv "$CRON_TAG" "$current" >"$next" || true
  crontab "$next"
  rm -f "$current" "$next"
}

check_prerequisites

if [[ "${1:-}" == "--check" ]]; then
  echo "preflight=ok"
  echo "scheduled_local_time=$EXPECTED_LOCAL_DATE $SCHEDULED_LOCAL_TIME $EXPECTED_TIMEZONE"
  echo "case=$CASES_DIR/$CASE_NAME"
  echo "parallel=$PARALLEL"
  echo "model=$MODEL"
  echo "coqc=$ROCQ_BIN_DIR/coqc"
  echo "coqtop=$ROCQ_BIN_DIR/coqtop"
  echo "rocq=$ROCQ_BIN_DIR/rocq"
  echo "worker_path=$WORKER_PATH"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  exit 0
fi
if [[ $# -ne 0 ]]; then
  echo "Usage: $(basename "$0") [--check]" >&2
  exit 2
fi

if [[ "$(date +%F)" != "$EXPECTED_LOCAL_DATE" ]]; then
  echo "ERROR: refusing launch outside scheduled local date $EXPECTED_LOCAL_DATE (current: $(date --iso-8601=seconds))" >&2
  exit 3
fi

opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

mkdir -p "$SCHEDULE_DIR" "$RESULTS_ROOT/supervisor"
exec 9>"$LOCK_FILE"
if ! flock -n 9; then
  echo "Another scheduled launcher instance is active; exiting."
  exit 0
fi
if [[ -e "$STARTED_MARKER" ]]; then
  echo "Scheduled experiment was already launched at $(cat "$STARTED_MARKER"); exiting."
  remove_own_cron_entry || true
  exit 0
fi

date --iso-8601=seconds >"$STARTED_MARKER"
remove_own_cron_entry || echo "WARNING: could not remove completed one-time cron entry" >&2

STAMP="$(date +%Y%m%d_%H%M%S)"
SUPERVISOR_DIR="$RESULTS_ROOT/supervisor/${CASE_NAME}_deepseek_v4_flash_3x_${STAMP}"
mkdir -p "$SUPERVISOR_DIR"

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

{
  echo "schedule_id=$SCHEDULE_ID"
  echo "scheduled_local_time=$EXPECTED_LOCAL_DATE $SCHEDULED_LOCAL_TIME $EXPECTED_TIMEZONE"
  echo "case=$CASES_DIR/$CASE_NAME"
  echo "parallel=$PARALLEL"
  echo "model=$MODEL"
  echo "coqc=$ROCQ_BIN_DIR/coqc"
  echo "coqtop=$ROCQ_BIN_DIR/coqtop"
  echo "rocq=$ROCQ_BIN_DIR/rocq"
  echo "worker_path=$WORKER_PATH"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  echo "run_timeout_seconds=$RUN_TIMEOUT_SECONDS"
  echo "model_response_timeout_seconds=$MODEL_RESPONSE_TIMEOUT_SECONDS"
  echo "results_root=$RESULTS_ROOT"
  echo "full_prosa_source_dir=$FULL_PROSA_SOURCE_DIR"
  echo "started_at=$(date --iso-8601=seconds)"
} >"$SUPERVISOR_DIR/config.txt"

echo "supervisor_dir=$SUPERVISOR_DIR"
echo "Launching $PARALLEL independent proofs for $CASE_NAME with $MODEL"

for worker_index in $(seq 1 "$PARALLEL"); do
  WORKER_ROOT="$SUPERVISOR_DIR/worker_$worker_index"
  WORKER_DATA_HOME="$WORKER_ROOT/data"
  WORKER_STATE_HOME="$WORKER_ROOT/state"
  WORKER_CACHE_HOME="$WORKER_ROOT/cache"
  WORKER_LOG="$SUPERVISOR_DIR/worker_${worker_index}.log"
  RESULT_PREFIX="our_casestudy_fullprosa_theorem6_deepseek_v4_flash_run${worker_index}"

  mkdir -p "$WORKER_DATA_HOME/opencode" "$WORKER_STATE_HOME/opencode" "$WORKER_CACHE_HOME"
  install -m 600 "$AUTH_SOURCE" "$WORKER_DATA_HOME/opencode/auth.json"

  echo "[launch] worker=$worker_index model=$MODEL result_prefix=$RESULT_PREFIX log=$WORKER_LOG"
  env -u OPENCODE_MODEL \
    "PATH=$WORKER_PATH" \
    BUN_BIN="$BUN_BIN" \
    XDG_DATA_HOME="$WORKER_DATA_HOME" \
    XDG_STATE_HOME="$WORKER_STATE_HOME" \
    XDG_CACHE_HOME="$WORKER_CACHE_HOME" \
    OPENCODE_RUN_NOHUP=0 \
    OPENCODE_RESULTS_ROOT="$RESULTS_ROOT" \
    OPENCODE_RESULT_PREFIX="$RESULT_PREFIX" \
    "$PYTHON_BIN" "$SERIAL_RUNNER" \
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
      "$CASE_NAME" >"$WORKER_LOG" 2>&1 &

  worker_pid="$!"
  WORKER_PIDS+=("$worker_pid")
  WORKER_IDS+=("$worker_index")
  echo "worker_${worker_index}_pid=$worker_pid" >>"$SUPERVISOR_DIR/pids.txt"

  if [[ "$worker_index" -lt "$PARALLEL" ]] && [[ "$LAUNCH_STAGGER_SECONDS" -gt 0 ]]; then
    sleep "$LAUNCH_STAGGER_SECONDS"
  fi
done

overall_status=0
for worker_offset in "${!WORKER_PIDS[@]}"; do
  set +e
  wait "${WORKER_PIDS[$worker_offset]}"
  worker_status="$?"
  set -e
  worker_index="${WORKER_IDS[$worker_offset]}"
  echo "worker_${worker_index}_status=$worker_status" >>"$SUPERVISOR_DIR/status.txt"
  if [[ "$worker_status" -ne 0 ]]; then
    overall_status=1
  fi
done

echo "finished_at=$(date --iso-8601=seconds)" >>"$SUPERVISOR_DIR/status.txt"
echo "overall_status=$overall_status" >>"$SUPERVISOR_DIR/status.txt"
echo "[finished] supervisor_dir=$SUPERVISOR_DIR status=$overall_status"
exit "$overall_status"
