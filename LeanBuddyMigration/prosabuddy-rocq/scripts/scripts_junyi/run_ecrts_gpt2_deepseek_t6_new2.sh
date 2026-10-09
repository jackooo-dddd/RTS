#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$SCRIPT_DIR/opencode_runner_config.sh"
opencode_config_load
opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

PYTHON_BIN="${PYTHON_BIN:-/usr/bin/python3}"
RUNNER="${OPENCODE_SERIAL_RUNNER:-/home/junyi/experiment/scripts/run_casestudy_our_minprosa.py}"
OPENCODE_BIN="${OPENCODE_BIN:-/home/junyi/experiment/scripts/opencode_our_local.sh}"
CASES_DIR="${OPENCODE_CASESTUDY_DIR:-/home/junyi/dataset/Case_Study}"
FULL_PROSA_SOURCE_DIR="${OPENCODE_FULL_PROSA_SOURCE_DIR:-/home/junyi/prosabuddy/prosaworkspace}"
RESULTS_ROOT="${OPENCODE_RESULTS_ROOT:-/home/junyi/results_rebuttal}"
AUTH_SOURCE="${OPENCODE_AUTH_SOURCE:-/home/junyi/.local/share/opencode/auth.json}"
ROCQ_BIN_DIR="${OPENCODE_ROCQ_BIN_DIR:-/home/junyi/.opam/rocq-4.14/bin}"
BUN_BIN="${BUN_BIN:-/home/junyi/.bun/bin/bun}"
WORKER_PATH="$ROCQ_BIN_DIR:/home/junyi/.bun/bin:/home/junyi/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

MAX_TOTAL_TOKENS="${OPENCODE_MAX_TOTAL_TOKENS:-80000000}"
MAX_RETRIES="${OPENCODE_MAX_RETRIES:-20}"
RUN_TIMEOUT_SECONDS="${OPENCODE_RUN_TIMEOUT_SECONDS:-43200}"
MODEL_RESPONSE_TIMEOUT_SECONDS="${OPENCODE_MODEL_RESPONSE_TIMEOUT_SECONDS:-600}"
LAUNCH_STAGGER_SECONDS="${OPENCODE_LAUNCH_STAGGER_SECONDS:-2}"
GPT_MODEL="${OPENCODE_GPT_MODEL:-codexproxy/gpt-5.4}"
GPT_MODEL_ID="${GPT_MODEL#*/}"
GPT_VARIANT="${OPENCODE_GPT_VARIANT:-xhigh}"
GPT_REASONING_EFFORT="${OPENCODE_GPT_REASONING_EFFORT:-$GPT_VARIANT}"
GPT_WORKER_TAG="${OPENCODE_GPT_WORKER_TAG:-gpt54}"
DEEPSEEK_MODEL="${OPENCODE_DEEPSEEK_MODEL:-deepseek/deepseek-v4-flash}"
DEEPSEEK_CASE_NAME="${OPENCODE_DEEPSEEK_CASE_NAME:-2005-ECRTS-Theorem6}"
DEEPSEEK_WORKER_TAG="${OPENCODE_DEEPSEEK_WORKER_TAG:-deepseek_t6}"
DEEPSEEK_CASE_NAME_1="${OPENCODE_DEEPSEEK_CASE_NAME_1:-$DEEPSEEK_CASE_NAME}"
DEEPSEEK_CASE_NAME_2="${OPENCODE_DEEPSEEK_CASE_NAME_2:-$DEEPSEEK_CASE_NAME}"
DEEPSEEK_WORKER_NAME_1="${OPENCODE_DEEPSEEK_WORKER_NAME_1:-${DEEPSEEK_WORKER_TAG}_new1}"
DEEPSEEK_WORKER_NAME_2="${OPENCODE_DEEPSEEK_WORKER_NAME_2:-${DEEPSEEK_WORKER_TAG}_new2}"
SUPERVISOR_TAG="${OPENCODE_SUPERVISOR_TAG:-ECRTS_gpt2_deepseek_t6_new2}"

WORKER_NAMES=("${GPT_WORKER_TAG}_l3" "${GPT_WORKER_TAG}_l4" "$DEEPSEEK_WORKER_NAME_1" "$DEEPSEEK_WORKER_NAME_2")
CASE_NAMES=(2005-ECRTS-Lemma3 2005-ECRTS-Lemma4 "$DEEPSEEK_CASE_NAME_1" "$DEEPSEEK_CASE_NAME_2")
MODELS=("$GPT_MODEL" "$GPT_MODEL" "$DEEPSEEK_MODEL" "$DEEPSEEK_MODEL")
VARIANTS=("$GPT_VARIANT" "$GPT_VARIANT" "" "")

check_prerequisites() {
  local required case_name resolved
  for required in \
    "$PYTHON_BIN" "$RUNNER" "$OPENCODE_BIN" "$AUTH_SOURCE" "$BUN_BIN" \
    "$ROCQ_BIN_DIR/coqc" "$ROCQ_BIN_DIR/coqtop" "$ROCQ_BIN_DIR/rocq" \
    "$FULL_PROSA_SOURCE_DIR"; do
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
  for case_name in "${CASE_NAMES[@]}"; do
    if [[ ! -d "$CASES_DIR/$case_name" ]]; then
      echo "ERROR: case study not found: $CASES_DIR/$case_name" >&2
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
  if ! grep -q '"deepseek"' "$AUTH_SOURCE"; then
    echo "ERROR: DeepSeek authentication is absent from $AUTH_SOURCE" >&2
    return 1
  fi
  if ! grep -q '"codexproxy"' "$AUTH_SOURCE"; then
    echo "ERROR: codexproxy authentication is absent from $AUTH_SOURCE" >&2
    return 1
  fi
}

check_prerequisites

if [[ "${1:-}" == "--check" ]]; then
  echo "preflight=ok"
  echo "workers=4"
  echo "gpt_workers=2005-ECRTS-Lemma3,2005-ECRTS-Lemma4"
  echo "deepseek_workers=$DEEPSEEK_CASE_NAME_1,$DEEPSEEK_CASE_NAME_2"
  echo "gpt_model=$GPT_MODEL"
  echo "gpt_variant=$GPT_VARIANT"
  echo "deepseek_model=$DEEPSEEK_MODEL"
  echo "coqc=$ROCQ_BIN_DIR/coqc"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
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

  # Every worker is launched under its own session/process group. Terminate
  # the whole group so an opencode/texlab descendant cannot survive after its
  # Python runner or this supervisor exits.
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
  echo "workers=4"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  echo "run_timeout_seconds=$RUN_TIMEOUT_SECONDS"
  echo "model_response_timeout_seconds=$MODEL_RESPONSE_TIMEOUT_SECONDS"
  echo "coqc=$ROCQ_BIN_DIR/coqc"
  echo "gpt_model=$GPT_MODEL"
  echo "gpt_variant=$GPT_VARIANT"
  echo "gpt_reasoning_effort=$GPT_REASONING_EFFORT"
  echo "deepseek_model=$DEEPSEEK_MODEL"
  echo "started_at=$(date --iso-8601=seconds)"
  for worker_offset in "${!WORKER_NAMES[@]}"; do
    echo "worker_$((worker_offset + 1))=${WORKER_NAMES[$worker_offset]}|${CASE_NAMES[$worker_offset]}|${MODELS[$worker_offset]}|${VARIANTS[$worker_offset]:-default}"
  done
} >"$SUPERVISOR_DIR/config.txt"

echo "supervisor_dir=$SUPERVISOR_DIR"
for worker_offset in "${!WORKER_NAMES[@]}"; do
  worker_name="${WORKER_NAMES[$worker_offset]}"
  case_name="${CASE_NAMES[$worker_offset]}"
  model="${MODELS[$worker_offset]}"
  variant="${VARIANTS[$worker_offset]}"
  worker_root="$SUPERVISOR_DIR/$worker_name"
  worker_log="$SUPERVISOR_DIR/$worker_name.log"
  result_prefix="our_casestudy_fullprosa_post_repair_${worker_name}"
  variant_args=()
  provider_args=()

  mkdir -p "$worker_root/data/opencode" "$worker_root/state/opencode" "$worker_root/cache"
  install -m 600 "$AUTH_SOURCE" "$worker_root/data/opencode/auth.json"
  if [[ -n "$variant" ]]; then
    variant_args=(--variant "$variant")
    provider_config="$(printf '{"provider":{"codexproxy":{"models":{"%s":{"variants":{"%s":{"reasoningEffort":"%s"}}}}}}}' \
      "$GPT_MODEL_ID" "$variant" "$GPT_REASONING_EFFORT")"
    provider_args=("OPENCODE_CONFIG_CONTENT=$provider_config")
  fi

  echo "[launch] worker=$worker_name case=$case_name model=$model variant=${variant:-default} log=$worker_log"
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
    "${provider_args[@]}" \
    "$PYTHON_BIN" "$RUNNER" \
      --model "$model" \
      "${variant_args[@]}" \
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
  WORKER_IDS+=("$worker_name")
  printf '%s=%s\n' "$worker_name" "$worker_pid" >>"$SUPERVISOR_DIR/pids.txt"
  if [[ "$worker_offset" -lt 3 ]] && [[ "$LAUNCH_STAGGER_SECONDS" -gt 0 ]]; then
    sleep "$LAUNCH_STAGGER_SECONDS"
  fi
done

overall_status=0
for worker_offset in "${!WORKER_PIDS[@]}"; do
  set +e
  wait "${WORKER_PIDS[$worker_offset]}"
  worker_status="$?"
  set -e
  # The direct runner may have exited while a descendant was still alive.
  # Reap the entire worker group before recording the worker as finished.
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
