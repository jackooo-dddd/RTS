#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$SCRIPT_DIR/opencode_runner_config.sh"
opencode_config_load
opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

PYTHON_BIN="/usr/bin/python3"
RUNNER="/home/junyi/experiment/scripts/run_casestudy_our_minprosa.py"
OPENCODE_BIN="/home/junyi/experiment/scripts/opencode_our_local.sh"
CASES_DIR="/home/junyi/dataset/Case_Study"
FULL_PROSA_SOURCE_DIR="/home/junyi/prosabuddy/prosaworkspace"
RESULTS_ROOT="/home/junyi/results_rebuttal"
AUTH_SOURCE="/home/junyi/.local/share/opencode/auth.json"
ROCQ_BIN_DIR="/home/junyi/.opam/rocq-4.14/bin"
BUN_BIN="/home/junyi/.bun/bin/bun"
WORKER_PATH="$ROCQ_BIN_DIR:/home/junyi/.bun/bin:/home/junyi/.local/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

RUN3_DIR="$RESULTS_ROOT/our_casestudy_fullprosa_theorem6_deepseek_v4_flash_run3_20260812_040005"
RUN3_XDG_ROOT="$RESULTS_ROOT/supervisor/2005-ECRTS-Theorem6_deepseek_v4_flash_3x_20260812_040001/worker_3"

MAX_TOTAL_TOKENS="80000000"
MAX_RETRIES="20"
RUN_TIMEOUT_SECONDS="43200"
MODEL_RESPONSE_TIMEOUT_SECONDS="600"

check_prerequisites() {
  local required resolved
  for required in \
    "$PYTHON_BIN" "$RUNNER" "$OPENCODE_BIN" "$AUTH_SOURCE" "$BUN_BIN" \
    "$ROCQ_BIN_DIR/coqc" "$ROCQ_BIN_DIR/coqtop" "$ROCQ_BIN_DIR/rocq" \
    "$FULL_PROSA_SOURCE_DIR" "$CASES_DIR/2005-ECRTS-Lemma3" \
    "$CASES_DIR/2005-ECRTS-Lemma4" "$CASES_DIR/2005-ECRTS-Theorem6" \
    "$RUN3_DIR/config.json" "$RUN3_DIR/summary.json" "$RUN3_XDG_ROOT/data"; do
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
  echo "workers=5"
  echo "gpt_workers=2005-ECRTS-Lemma3,2005-ECRTS-Lemma4"
  echo "deepseek_resume=$RUN3_DIR"
  echo "deepseek_new_workers=2x2005-ECRTS-Theorem6"
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
SUPERVISOR_DIR="$RESULTS_ROOT/supervisor/ECRTS_gpt2_deepseek_t6_resume_plus2_$STAMP"
mkdir -p "$SUPERVISOR_DIR"
printf '%s\n' "$SUPERVISOR_DIR" >"$RESULTS_ROOT/supervisor/ECRTS_gpt2_deepseek_t6_resume_plus2_latest.txt"

declare -a WORKER_PIDS=()
declare -a WORKER_NAMES=()

register_worker() {
  local name="$1"
  local pid="$2"
  WORKER_NAMES+=("$name")
  WORKER_PIDS+=("$pid")
  printf '%s=%s\n' "$name" "$pid" >>"$SUPERVISOR_DIR/pids.txt"
}

launch_new() {
  local name="$1"
  local case_name="$2"
  local model="$3"
  local variant="$4"
  local result_prefix="$5"
  local worker_root="$SUPERVISOR_DIR/$name"
  local worker_log="$SUPERVISOR_DIR/$name.log"
  local -a variant_args=()
  local -a provider_args=()

  mkdir -p "$worker_root/data/opencode" "$worker_root/state/opencode" "$worker_root/cache"
  install -m 600 "$AUTH_SOURCE" "$worker_root/data/opencode/auth.json"
  if [[ -n "$variant" ]]; then
    variant_args=(--variant "$variant")
    provider_args=('OPENCODE_CONFIG_CONTENT={"provider":{"codexproxy":{"models":{"gpt-5.4":{"variants":{"xhigh":{"reasoningEffort":"xhigh"}}}}}}}')
  fi

  env -u OPENCODE_MODEL -u OPENCODE_VARIANT \
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
  register_worker "$name" "$!"
}

launch_resume_run3() {
  local name="deepseek_t6_run3_resume"
  local worker_log="$SUPERVISOR_DIR/$name.log"

  env -u OPENCODE_MODEL -u OPENCODE_VARIANT \
    "PATH=$WORKER_PATH" \
    "BUN_BIN=$BUN_BIN" \
    "XDG_DATA_HOME=$RUN3_XDG_ROOT/data" \
    "XDG_STATE_HOME=$RUN3_XDG_ROOT/state" \
    "XDG_CACHE_HOME=$RUN3_XDG_ROOT/cache" \
    OPENCODE_RUN_NOHUP=0 \
    PYTHONUNBUFFERED=1 \
    "$PYTHON_BIN" "$RUNNER" \
      --model deepseek/deepseek-v4-flash \
      --resume-run-dir "$RUN3_DIR" \
      --fresh-session-on-resume \
      --reset-retries-on-resume \
      --run-timeout-seconds "$RUN_TIMEOUT_SECONDS" \
      --model-response-timeout-seconds "$MODEL_RESPONSE_TIMEOUT_SECONDS" \
      --max-total-tokens "$MAX_TOTAL_TOKENS" \
      --max-retries "$MAX_RETRIES" \
      --opencode-bin "$OPENCODE_BIN" \
      --trace-requests \
      2005-ECRTS-Theorem6 >"$worker_log" 2>&1 &
  register_worker "$name" "$!"
}

terminate_workers() {
  local pid
  for pid in "${WORKER_PIDS[@]:-}"; do
    if [[ -n "$pid" ]] && kill -0 "$pid" 2>/dev/null; then
      kill "$pid" 2>/dev/null || true
    fi
  done
}
trap 'terminate_workers; exit 130' INT TERM

{
  echo "workers=5"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  echo "run_timeout_seconds=$RUN_TIMEOUT_SECONDS"
  echo "model_response_timeout_seconds=$MODEL_RESPONSE_TIMEOUT_SECONDS"
  echo "coqc=$ROCQ_BIN_DIR/coqc"
  echo "started_at=$(date --iso-8601=seconds)"
} >"$SUPERVISOR_DIR/config.txt"

echo "supervisor_dir=$SUPERVISOR_DIR"
launch_new gpt54_l3 2005-ECRTS-Lemma3 codexproxy/gpt-5.4 xhigh our_casestudy_fullprosa_restart_gpt54_l3
launch_new gpt54_l4 2005-ECRTS-Lemma4 codexproxy/gpt-5.4 xhigh our_casestudy_fullprosa_restart_gpt54_l4
launch_resume_run3
launch_new deepseek_t6_new1 2005-ECRTS-Theorem6 deepseek/deepseek-v4-flash "" our_casestudy_fullprosa_restart_deepseek_t6_new1
launch_new deepseek_t6_new2 2005-ECRTS-Theorem6 deepseek/deepseek-v4-flash "" our_casestudy_fullprosa_restart_deepseek_t6_new2

overall_status=0
for index in "${!WORKER_PIDS[@]}"; do
  set +e
  wait "${WORKER_PIDS[$index]}"
  worker_status="$?"
  set -e
  printf '%s=%s\n' "${WORKER_NAMES[$index]}" "$worker_status" >>"$SUPERVISOR_DIR/status.txt"
  if [[ "$worker_status" -ne 0 ]]; then
    overall_status=1
  fi
done

echo "finished_at=$(date --iso-8601=seconds)" >>"$SUPERVISOR_DIR/status.txt"
echo "overall_status=$overall_status" >>"$SUPERVISOR_DIR/status.txt"
exit "$overall_status"
