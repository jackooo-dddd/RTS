#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

source "$SCRIPT_DIR/opencode_runner_config.sh"
opencode_config_load
opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

declare -a WORKER_INDEXES=(1 2)
if [[ $# -eq 2 && "$1" == "--worker-index" && "$2" =~ ^[12]$ ]]; then
    WORKER_INDEXES=("$2")
elif [[ $# -ne 0 ]]; then
    echo "Usage: $(basename "$0") [--worker-index 1|2]" >&2
    exit 2
fi

PYTHON_BIN="${PYTHON_BIN:-$(command -v python3)}"
SERIAL_RUNNER="${OPENCODE_SERIAL_RUNNER:-$SCRIPT_DIR/run_casestudy_our_minprosa.py}"
OPENCODE_BIN="${OPENCODE_BIN:-$SCRIPT_DIR/opencode_our_local.sh}"
CASES_DIR="${OPENCODE_CASESTUDY_DIR:-/home/junyi/dataset/Case_Study}"
FULL_PROSA_SOURCE_DIR="${OPENCODE_FULL_PROSA_SOURCE_DIR:-/home/junyi/prosabuddy/prosaworkspace}"
RESULTS_ROOT="${OPENCODE_RESULTS_ROOT:-/home/junyi/results_rebuttal}"
CASE_NAME="2005-ECRTS-Lemma3"
PARALLEL="${OPENCODE_PARALLEL:-2}"
MAX_TOTAL_TOKENS="${OPENCODE_MAX_TOTAL_TOKENS:-80000000}"
MAX_RETRIES="${OPENCODE_MAX_RETRIES:-8}"
RUN_TIMEOUT_SECONDS="${OPENCODE_RUN_TIMEOUT_SECONDS:-43200}"
LAUNCH_STAGGER_SECONDS="${OPENCODE_LAUNCH_STAGGER_SECONDS:-4}"
AUTH_SOURCE="${OPENCODE_AUTH_SOURCE:-${XDG_DATA_HOME:-$HOME/.local/share}/opencode/auth.json}"
MODEL_STATE_SOURCE="${OPENCODE_MODEL_STATE_SOURCE:-${XDG_STATE_HOME:-$HOME/.local/state}/opencode/model.json}"

if [[ "$PARALLEL" != "2" ]]; then
    echo "ERROR: this rebuttal experiment requires OPENCODE_PARALLEL=2 (got $PARALLEL)" >&2
    exit 2
fi
if [[ ! "$MAX_TOTAL_TOKENS" =~ ^[0-9]+$ ]] || [[ "$MAX_TOTAL_TOKENS" -ne 80000000 ]]; then
    echo "ERROR: OPENCODE_MAX_TOTAL_TOKENS must be 80000000 (got $MAX_TOTAL_TOKENS)" >&2
    exit 2
fi
if [[ ! "$MAX_RETRIES" =~ ^[0-9]+$ ]] || [[ "$MAX_RETRIES" -ne 8 ]]; then
    echo "ERROR: OPENCODE_MAX_RETRIES must be 8 (got $MAX_RETRIES)" >&2
    exit 2
fi
if [[ ! -x "$PYTHON_BIN" ]]; then
    echo "ERROR: Python executable not found: $PYTHON_BIN" >&2
    exit 1
fi
if [[ ! -f "$SERIAL_RUNNER" ]]; then
    echo "ERROR: serial runner not found: $SERIAL_RUNNER" >&2
    exit 1
fi
if [[ ! -x "$OPENCODE_BIN" ]]; then
    echo "ERROR: Prosabuddy runner not executable: $OPENCODE_BIN" >&2
    exit 1
fi
if [[ ! -d "$CASES_DIR/$CASE_NAME" ]]; then
    echo "ERROR: casestudy not found: $CASES_DIR/$CASE_NAME" >&2
    exit 1
fi
if [[ ! -d "$FULL_PROSA_SOURCE_DIR" ]]; then
    echo "ERROR: full Prosa source not found: $FULL_PROSA_SOURCE_DIR" >&2
    exit 1
fi
if [[ ! -f "$AUTH_SOURCE" ]]; then
    echo "ERROR: Prosabuddy auth source not found: $AUTH_SOURCE" >&2
    exit 1
fi
if [[ ! -f "$MODEL_STATE_SOURCE" ]]; then
    echo "ERROR: Prosabuddy model state not found: $MODEL_STATE_SOURCE" >&2
    exit 1
fi

mkdir -p "$RESULTS_ROOT"
STAMP="$(date +%Y%m%d_%H%M%S)"
SUPERVISOR_DIR="$RESULTS_ROOT/supervisor/${CASE_NAME}_${STAMP}"
mkdir -p "$SUPERVISOR_DIR"

declare -a WORKER_PIDS=()
declare -a WORKER_LOGS=()

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
    echo "case=$CASE_NAME"
    echo "parallel=$PARALLEL"
    echo "launched_workers=${WORKER_INDEXES[*]}"
    echo "max_total_tokens=$MAX_TOTAL_TOKENS"
    echo "max_retries=$MAX_RETRIES"
    echo "run_timeout_seconds=$RUN_TIMEOUT_SECONDS"
    echo "results_root=$RESULTS_ROOT"
    echo "full_prosa_source_dir=$FULL_PROSA_SOURCE_DIR"
    echo "started_at=$(date --iso-8601=seconds)"
} >"$SUPERVISOR_DIR/config.txt"

for worker_offset in "${!WORKER_INDEXES[@]}"; do
    worker_index="${WORKER_INDEXES[$worker_offset]}"
    WORKER_ROOT="$SUPERVISOR_DIR/worker_${worker_index}"
    WORKER_DATA_HOME="$WORKER_ROOT/data"
    WORKER_STATE_HOME="$WORKER_ROOT/state"
    WORKER_LOG="$SUPERVISOR_DIR/worker_${worker_index}.log"
    RESULT_PREFIX="our_casestudy_fullprosa_rebuttal_run${worker_index}"

    mkdir -p "$WORKER_DATA_HOME/opencode" "$WORKER_STATE_HOME/opencode"
    install -m 600 "$AUTH_SOURCE" "$WORKER_DATA_HOME/opencode/auth.json"
    install -m 600 "$MODEL_STATE_SOURCE" "$WORKER_STATE_HOME/opencode/model.json"

    echo "[launch] worker=$worker_index result_prefix=$RESULT_PREFIX log=$WORKER_LOG"
    env -u OPENCODE_MODEL \
        XDG_DATA_HOME="$WORKER_DATA_HOME" \
        XDG_STATE_HOME="$WORKER_STATE_HOME" \
        OPENCODE_RUN_NOHUP=0 \
        OPENCODE_RESULTS_ROOT="$RESULTS_ROOT" \
        OPENCODE_RESULT_PREFIX="$RESULT_PREFIX" \
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

    WORKER_PIDS+=("$!")
    WORKER_LOGS+=("$WORKER_LOG")
    echo "worker_${worker_index}_pid=$!" >>"$SUPERVISOR_DIR/pids.txt"

    if [[ "$worker_offset" -lt "$((${#WORKER_INDEXES[@]} - 1))" ]] && [[ "$LAUNCH_STAGGER_SECONDS" -gt 0 ]]; then
        sleep "$LAUNCH_STAGGER_SECONDS"
    fi
done

overall_status=0
for worker_offset in "${!WORKER_PIDS[@]}"; do
    set +e
    wait "${WORKER_PIDS[$worker_offset]}"
    worker_status=$?
    set -e
    if [[ "$worker_status" -ne 0 ]]; then
        overall_status=1
    fi
    worker_index="${WORKER_INDEXES[$worker_offset]}"
    echo "worker_${worker_index}_status=$worker_status" >>"$SUPERVISOR_DIR/status.txt"
done

echo "finished_at=$(date --iso-8601=seconds)" >>"$SUPERVISOR_DIR/status.txt"
echo "overall_status=$overall_status" >>"$SUPERVISOR_DIR/status.txt"
echo "[finished] supervisor_dir=$SUPERVISOR_DIR status=$overall_status"
exit "$overall_status"
