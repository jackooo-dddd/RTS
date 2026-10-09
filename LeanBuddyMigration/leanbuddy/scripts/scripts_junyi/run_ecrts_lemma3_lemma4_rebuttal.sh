#!/usr/bin/env bash
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
MAX_TOTAL_TOKENS="${OPENCODE_MAX_TOTAL_TOKENS:-80000000}"
MAX_RETRIES="${OPENCODE_MAX_RETRIES:-8}"
RUN_TIMEOUT_SECONDS="${OPENCODE_RUN_TIMEOUT_SECONDS:-43200}"
MODEL_RESPONSE_TIMEOUT_SECONDS="${OPENCODE_MODEL_RESPONSE_TIMEOUT_SECONDS:-600}"
LAUNCH_STAGGER_SECONDS="${OPENCODE_LAUNCH_STAGGER_SECONDS:-4}"
AUTH_SOURCE="${OPENCODE_AUTH_SOURCE:-${XDG_DATA_HOME:-$HOME/.local/share}/opencode/auth.json}"
MODEL_STATE_SOURCE="${OPENCODE_MODEL_STATE_SOURCE:-${XDG_STATE_HOME:-$HOME/.local/state}/opencode/model.json}"

declare -a WORKER_SPECS=(
  "lemma3|2005-ECRTS-Lemma3|our_casestudy_fullprosa_rebuttal_lemma3"
  "lemma4|2005-ECRTS-Lemma4|our_casestudy_fullprosa_rebuttal_lemma4"
)

CHECK_ONLY=0
if [[ "${1:-}" == "--check" && $# -eq 1 ]]; then
  CHECK_ONLY=1
elif [[ $# -ne 0 ]]; then
  echo "Usage: $(basename "$0") [--check]" >&2
  exit 2
fi

for required in "$SERIAL_RUNNER" "$OPENCODE_BIN" "$AUTH_SOURCE" "$MODEL_STATE_SOURCE"; do
  if [[ ! -e "$required" ]]; then
    echo "ERROR: required file not found: $required" >&2
    exit 1
  fi
done
if [[ ! "$MAX_TOTAL_TOKENS" =~ ^[0-9]+$ ]] || [[ "$MAX_TOTAL_TOKENS" -ne 80000000 ]]; then
  echo "ERROR: OPENCODE_MAX_TOTAL_TOKENS must be 80000000 (got $MAX_TOTAL_TOKENS)" >&2
  exit 2
fi
if [[ ! "$MAX_RETRIES" =~ ^[0-9]+$ ]] || [[ "$MAX_RETRIES" -ne 8 ]]; then
  echo "ERROR: OPENCODE_MAX_RETRIES must be 8 (got $MAX_RETRIES)" >&2
  exit 2
fi

for spec in "${WORKER_SPECS[@]}"; do
  case_name="$(cut -d'|' -f2 <<<"$spec")"
  if [[ ! -d "$CASES_DIR/$case_name" ]]; then
    echo "ERROR: casestudy not found: $CASES_DIR/$case_name" >&2
    exit 1
  fi
done

if [[ "$CHECK_ONLY" -eq 1 ]]; then
  echo "preflight=ok"
  echo "cases=2005-ECRTS-Lemma3 2005-ECRTS-Lemma4"
  echo "parallel=${#WORKER_SPECS[@]}"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  exit 0
fi

mkdir -p "$RESULTS_ROOT/supervisor"
STAMP="$(date +%Y%m%d_%H%M%S)"
SUPERVISOR_DIR="$RESULTS_ROOT/supervisor/2005-ECRTS-Lemma3_Lemma4_${STAMP}"
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
  echo "cases=2005-ECRTS-Lemma3 2005-ECRTS-Lemma4"
  echo "parallel=2"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  echo "run_timeout_seconds=$RUN_TIMEOUT_SECONDS"
  echo "model_response_timeout_seconds=$MODEL_RESPONSE_TIMEOUT_SECONDS"
  echo "results_root=$RESULTS_ROOT"
  echo "full_prosa_source_dir=$FULL_PROSA_SOURCE_DIR"
  echo "started_at=$(date --iso-8601=seconds)"
} >"$SUPERVISOR_DIR/config.txt"

echo "supervisor_dir=$SUPERVISOR_DIR"

for worker_offset in "${!WORKER_SPECS[@]}"; do
  spec="${WORKER_SPECS[$worker_offset]}"
  worker_id="$(cut -d'|' -f1 <<<"$spec")"
  case_name="$(cut -d'|' -f2 <<<"$spec")"
  result_prefix="$(cut -d'|' -f3 <<<"$spec")"
  worker_root="$SUPERVISOR_DIR/worker_$worker_id"
  worker_data_home="$worker_root/data"
  worker_state_home="$worker_root/state"
  worker_log="$SUPERVISOR_DIR/worker_$worker_id.log"

  mkdir -p "$worker_data_home/opencode" "$worker_state_home/opencode"
  install -m 600 "$AUTH_SOURCE" "$worker_data_home/opencode/auth.json"
  install -m 600 "$MODEL_STATE_SOURCE" "$worker_state_home/opencode/model.json"

  echo "[launch] worker=$worker_id case=$case_name result_prefix=$result_prefix log=$worker_log"
  env -u OPENCODE_MODEL \
    XDG_DATA_HOME="$worker_data_home" \
    XDG_STATE_HOME="$worker_state_home" \
    OPENCODE_RUN_NOHUP=0 \
    OPENCODE_RESULTS_ROOT="$RESULTS_ROOT" \
    OPENCODE_RESULT_PREFIX="$result_prefix" \
    "$PYTHON_BIN" "$SERIAL_RUNNER" \
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
      "$case_name" >"$worker_log" 2>&1 &

  worker_pid="$!"
  WORKER_PIDS+=("$worker_pid")
  WORKER_IDS+=("$worker_id")
  echo "worker_${worker_id}_pid=$worker_pid" >>"$SUPERVISOR_DIR/pids.txt"
  echo "worker_${worker_id}_case=$case_name" >>"$SUPERVISOR_DIR/pids.txt"

  if [[ "$worker_offset" -lt "$((${#WORKER_SPECS[@]} - 1))" ]] && [[ "$LAUNCH_STAGGER_SECONDS" -gt 0 ]]; then
    sleep "$LAUNCH_STAGGER_SECONDS"
  fi
done

overall_status=0
for worker_offset in "${!WORKER_PIDS[@]}"; do
  set +e
  wait "${WORKER_PIDS[$worker_offset]}"
  worker_status="$?"
  set -e
  worker_id="${WORKER_IDS[$worker_offset]}"
  echo "worker_${worker_id}_status=$worker_status" >>"$SUPERVISOR_DIR/status.txt"
  if [[ "$worker_status" -ne 0 ]]; then
    overall_status=1
  fi
done

echo "finished_at=$(date --iso-8601=seconds)" >>"$SUPERVISOR_DIR/status.txt"
echo "overall_status=$overall_status" >>"$SUPERVISOR_DIR/status.txt"
echo "[finished] supervisor_dir=$SUPERVISOR_DIR status=$overall_status"
exit "$overall_status"
