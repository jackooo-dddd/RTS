#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$SCRIPT_DIR/opencode_runner_config.sh"
opencode_config_load
opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

PYTHON_BIN="${PYTHON_BIN:-/usr/bin/python3}"
SERIAL_RUNNER="${OPENCODE_SERIAL_RUNNER:-$SCRIPT_DIR/run_casestudy_our_minprosa.py}"
OPENCODE_BIN="${OPENCODE_BIN:-$SCRIPT_DIR/opencode_our_local.sh}"
CASES_DIR="${OPENCODE_CASESTUDY_DIR:-/home/junyi/dataset/Case_Study}"
FULL_PROSA_SOURCE_DIR="${OPENCODE_FULL_PROSA_SOURCE_DIR:-/home/junyi/prosabuddy/prosaworkspace}"
RESULTS_ROOT="${OPENCODE_RESULTS_ROOT:-/home/junyi/results_rebuttal}"
AUTH_SOURCE="${OPENCODE_AUTH_SOURCE:-$HOME/.local/share/opencode/auth.json}"
ROCQ_BIN_DIR="${OPENCODE_ROCQ_BIN_DIR:-/home/junyi/.opam/rocq-4.14/bin}"

MAX_TOTAL_TOKENS="${OPENCODE_MAX_TOTAL_TOKENS:-80000000}"
MAX_RETRIES="${OPENCODE_MAX_RETRIES:-20}"
RUN_TIMEOUT_SECONDS="${OPENCODE_RUN_TIMEOUT_SECONDS:-43200}"
MODEL_RESPONSE_TIMEOUT_SECONDS="${OPENCODE_MODEL_RESPONSE_TIMEOUT_SECONDS:-600}"
LAUNCH_STAGGER_SECONDS="${OPENCODE_LAUNCH_STAGGER_SECONDS:-2}"

MIXED4_PROFILE="${OPENCODE_MIXED4_PROFILE:-lemma3_lemma4}"
case "$MIXED4_PROFILE" in
  lemma3_lemma4)
    WORKER_NAMES=(gpt54_l4 deepseek_l3 deepseek_l4a deepseek_l4b)
    CASE_NAMES=(2005-ECRTS-Lemma4 2005-ECRTS-Lemma3 2005-ECRTS-Lemma4 2005-ECRTS-Lemma4)
    ;;
  lemma4_theorem6)
    WORKER_NAMES=(gpt54_l4 deepseek_l4a deepseek_l4b deepseek_t6)
    CASE_NAMES=(2005-ECRTS-Lemma4 2005-ECRTS-Lemma4 2005-ECRTS-Lemma4 2005-ECRTS-Theorem6)
    ;;
  *)
    echo "ERROR: unsupported OPENCODE_MIXED4_PROFILE: $MIXED4_PROFILE" >&2
    exit 2
    ;;
esac
MODELS=(codexproxy/gpt-5.4 deepseek/deepseek-v4-flash deepseek/deepseek-v4-flash deepseek/deepseek-v4-flash)
VARIANTS=(xhigh "" "" "")

check_prerequisites() {
  local required case_name
  for required in "$PYTHON_BIN" "$SERIAL_RUNNER" "$OPENCODE_BIN" "$AUTH_SOURCE" "$ROCQ_BIN_DIR/coqc"; do
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
  for case_name in "${CASE_NAMES[@]}"; do
    if [[ ! -d "$CASES_DIR/$case_name" ]]; then
      echo "ERROR: case study not found: $CASES_DIR/$case_name" >&2
      return 1
    fi
  done
  if [[ ! -d "$FULL_PROSA_SOURCE_DIR" ]]; then
    echo "ERROR: full Prosa source not found: $FULL_PROSA_SOURCE_DIR" >&2
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
  echo "profile=$MIXED4_PROFILE"
  echo "workers=${#WORKER_NAMES[@]}"
  echo "profile=$MIXED4_PROFILE"
  echo "gpt_model=${MODELS[0]}"
  echo "gpt_variant=${VARIANTS[0]}"
  echo "deepseek_model=${MODELS[1]}"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  echo "coqc=$ROCQ_BIN_DIR/coqc"
  exit 0
fi
if [[ $# -ne 0 ]]; then
  echo "Usage: $(basename "$0") [--check]" >&2
  exit 2
fi

STAMP="$(date +%Y%m%d_%H%M%S)"
SUPERVISOR_DIR="$RESULTS_ROOT/supervisor/ECRTS_mixed4_${STAMP}"
mkdir -p "$SUPERVISOR_DIR"
printf '%s\n' "$SUPERVISOR_DIR" >"$RESULTS_ROOT/supervisor/ECRTS_mixed4_latest.txt"

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
  echo "workers=${#WORKER_NAMES[@]}"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS"
  echo "max_retries=$MAX_RETRIES"
  echo "run_timeout_seconds=$RUN_TIMEOUT_SECONDS"
  echo "model_response_timeout_seconds=$MODEL_RESPONSE_TIMEOUT_SECONDS"
  echo "results_root=$RESULTS_ROOT"
  echo "cases_dir=$CASES_DIR"
  echo "full_prosa_source_dir=$FULL_PROSA_SOURCE_DIR"
  echo "coqc=$ROCQ_BIN_DIR/coqc"
  echo "started_at=$(date --iso-8601=seconds)"
  for worker_offset in "${!WORKER_NAMES[@]}"; do
    echo "worker_$((worker_offset + 1))=${WORKER_NAMES[$worker_offset]}|${CASE_NAMES[$worker_offset]}|${MODELS[$worker_offset]}|${VARIANTS[$worker_offset]:-default}"
  done
} >"$SUPERVISOR_DIR/config.txt"

echo "supervisor_dir=$SUPERVISOR_DIR"
echo "Launching ${#WORKER_NAMES[@]} independent proof workers"

for worker_offset in "${!WORKER_NAMES[@]}"; do
  worker_index="$((worker_offset + 1))"
  worker_name="${WORKER_NAMES[$worker_offset]}"
  case_name="${CASE_NAMES[$worker_offset]}"
  model="${MODELS[$worker_offset]}"
  variant="${VARIANTS[$worker_offset]}"
  worker_root="$SUPERVISOR_DIR/$worker_name"
  worker_data_home="$worker_root/data"
  worker_state_home="$worker_root/state"
  worker_cache_home="$worker_root/cache"
  worker_log="$SUPERVISOR_DIR/${worker_name}.log"
  result_prefix="our_casestudy_fullprosa_mixed4_${worker_name}"
  variant_args=()
  provider_config_args=()

  mkdir -p "$worker_data_home/opencode" "$worker_state_home/opencode" "$worker_cache_home"
  install -m 600 "$AUTH_SOURCE" "$worker_data_home/opencode/auth.json"

  if [[ -n "$variant" ]]; then
    variant_args=(--variant "$variant")
    # Custom OpenAI-compatible providers do not infer xhigh automatically.
    # Publish the requested variant explicitly so --variant changes the API request.
    provider_config_args=(
      'OPENCODE_CONFIG_CONTENT={"provider":{"codexproxy":{"models":{"gpt-5.4":{"variants":{"xhigh":{"reasoningEffort":"xhigh"}}}}}}}'
    )
  fi

  echo "[launch] worker=$worker_name case=$case_name model=$model variant=${variant:-default} log=$worker_log"
  env -u OPENCODE_MODEL -u OPENCODE_VARIANT \
    "PATH=$ROCQ_BIN_DIR:$PATH" \
    "XDG_DATA_HOME=$worker_data_home" \
    "XDG_STATE_HOME=$worker_state_home" \
    "XDG_CACHE_HOME=$worker_cache_home" \
    OPENCODE_RUN_NOHUP=0 \
    OPENCODE_OUR_DIRECT_PROSA_PROBE=0 \
    "OPENCODE_RESULTS_ROOT=$RESULTS_ROOT" \
    "OPENCODE_RESULT_PREFIX=$result_prefix" \
    "${provider_config_args[@]}" \
    "$PYTHON_BIN" "$SERIAL_RUNNER" \
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
  echo "$worker_name=$worker_pid" >>"$SUPERVISOR_DIR/pids.txt"

  if [[ "$worker_index" -lt "${#WORKER_NAMES[@]}" ]] && [[ "$LAUNCH_STAGGER_SECONDS" -gt 0 ]]; then
    sleep "$LAUNCH_STAGGER_SECONDS"
  fi
done

overall_status=0
for worker_offset in "${!WORKER_PIDS[@]}"; do
  set +e
  wait "${WORKER_PIDS[$worker_offset]}"
  worker_status="$?"
  set -e
  worker_name="${WORKER_IDS[$worker_offset]}"
  echo "$worker_name=$worker_status" >>"$SUPERVISOR_DIR/status.txt"
  if [[ "$worker_status" -ne 0 ]]; then
    overall_status=1
  fi
done

echo "finished_at=$(date --iso-8601=seconds)" >>"$SUPERVISOR_DIR/status.txt"
echo "overall_status=$overall_status" >>"$SUPERVISOR_DIR/status.txt"
echo "[finished] supervisor_dir=$SUPERVISOR_DIR status=$overall_status"
exit "$overall_status"
