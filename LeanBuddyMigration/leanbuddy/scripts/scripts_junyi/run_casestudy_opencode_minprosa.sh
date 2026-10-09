#!/usr/bin/env bash
# Parallel runner for OpenCode minimal-Prosa casestudy theorem proving.
#
# Each worker is pinned to one XDG_DATA_HOME account directory so that opencode
# sessions and credentials remain isolated per worker.
#
# Required:
#   --accounts-dir DIR   Directory containing account_0, account_1, ... or
#                        account-0, account-1, ... subdirs.
#
# Optional:
#   --model MODEL        Provider/model string (e.g. copilot/claude-sonnet-4)
#   --parallel N         Number of concurrent workers (default: 1)
#   --launch-stagger-seconds N   Delay between starting workers (default: 4)
#   --run-timeout-seconds N      Per-casestudy timeout (default: 43200)
#   --ratelimit-retry-wait-seconds N  Wait before retrying a rate-limited account (default: 1800)
#   --max-ratelimit-retries N         Max retries after rate limiting per casestudy/account (default: 8)
#   --opencode-bin PATH  Path to opencode binary (default: scripts/opencode_trace_local.sh)
#   --full-prosa         Copy the full prosa_v06 tree into the staged workspace as prosa/
#   --skill              Copy opencode-trace/.opencode/skill into the staged workspace and allow skill use
#   --trace-requests     Save full opencode request traces in each result directory
#
# Positional: one or more casestudy workspace names.
#
# Example:
#   ./scripts/run_casestudy_opencode_minprosa.sh \
#     --accounts-dir /data/opencode-accounts \
#     --model copilot/claude-sonnet-4 \
#     --parallel 4 \
#     2009-RTSS-Lemma3 2007-RTSS-Theorem1

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$PROJECT_ROOT/scripts/opencode_runner_config.sh"
opencode_config_load
opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

PYTHON_BIN="${PYTHON_BIN:-$PROJECT_ROOT/.venv/bin/python}"
RUNNER="${OPENCODE_SERIAL_RUNNER:-$PROJECT_ROOT/scripts/run_casestudy_opencode_minprosa.py}"
DEFAULT_OPENCODE_BIN="$PROJECT_ROOT/scripts/opencode_trace_local.sh"
RESULT_PREFIX="${OPENCODE_RESULT_PREFIX:-}"
PARALLEL_RESULT_PREFIX="${OPENCODE_PARALLEL_RESULT_PREFIX:-}"

# Defaults
MODEL="${OPENCODE_MODEL:-}"
PARALLEL=1
LAUNCH_STAGGER_SECONDS=4
RUN_TIMEOUT_SECONDS=43200
RATELIMIT_RETRY_WAIT_SECONDS=1800
MAX_RATELIMIT_RETRIES="${OPENCODE_MAX_RATELIMIT_RETRIES:-8}"
OPENCODE_BIN="${OPENCODE_BIN:-$DEFAULT_OPENCODE_BIN}"
ACCOUNTS_DIR=""
CASES_DIR="$PROJECT_ROOT/datasets_v06/casestudy_v06"
STAGE_FULL_CASESTUDY_WORKSPACE=0
FULL_PROSA=0
FULL_PROSA_SOURCE_DIR="${OPENCODE_FULL_PROSA_SOURCE_DIR:-$PROJECT_ROOT/prosa_v06}"
SEGMENTED_PROOF_WORKFLOW=0
ENABLE_SKILL=0
TRACE_REQUESTS=0
RESUME_RUN_DIR=""
FRESH_SESSION_ON_RESUME=0
CASESTUDIES=()
if opencode_config_bool_true "${OPENCODE_WITH_PAPER:-0}"; then
    STAGE_FULL_CASESTUDY_WORKSPACE=1
    SEGMENTED_PROOF_WORKFLOW=1
fi
if opencode_config_bool_true "${OPENCODE_FULL_PROSA:-0}"; then
    FULL_PROSA=1
fi
if opencode_config_bool_true "${OPENCODE_ENABLE_SKILL:-0}"; then
    ENABLE_SKILL=1
fi
if opencode_config_bool_true "${OPENCODE_TRACE_REQUESTS:-0}"; then
    TRACE_REQUESTS=1
fi

normalize_tag_component() {
    local value="$1"

    if [[ "$value" == */* ]]; then
        value="${value##*/}"
    fi

    value="$(printf '%s' "$value" | tr '[:upper:]' '[:lower:]' | sed -E 's/[^a-z0-9._-]+/-/g; s/^-+//; s/-+$//')"
    if [[ -z "$value" ]]; then
        value="default"
    fi
    printf '%s' "$value"
}

build_experiment_tag() {
    local prosa_tag
    local model_tag
    local skill_tag

    prosa_tag="minprosa"
    if [[ "$FULL_PROSA" -eq 1 ]]; then
        prosa_tag="fullprosa"
    fi

    model_tag="$(normalize_tag_component "${MODEL:-default}")"

    skill_tag="noskill"
    if [[ "$ENABLE_SKILL" -eq 1 ]]; then
        skill_tag="withskill"
    fi

    printf '%s_%s_%s' "$prosa_tag" "$model_tag" "$skill_tag"
}

usage() {
    cat <<'EOF'
Usage:
    ./scripts/run_casestudy_opencode_minprosa.sh \
        --accounts-dir DIR [OPTIONS] WORKSPACE_NAME [WORKSPACE_NAME ...]

Options:
    --accounts-dir DIR        Directory with account_0/, account_1/, ... or
                              account-0/, account-1/, ... subdirs.
                              Each subdir is used as XDG_DATA_HOME for one worker.
    --model MODEL             Provider/model (e.g. copilot/claude-sonnet-4).
    --cases-dir DIR           Casestudy root directory (default: datasets_v06/casestudy_v06).
    --parallel N              Number of concurrent workers (default: 1).
    --launch-stagger-seconds N  Delay between worker starts (default: 4).
    --run-timeout-seconds N   Per-casestudy timeout in seconds (default: 43200).
    --ratelimit-retry-wait-seconds N
                              Wait in seconds before retrying after a rate-limit error (default: 1800).
    --max-ratelimit-retries N
                              Max retries for rate-limit errors per casestudy/account (default: 8).
    --opencode-bin PATH       Path to opencode binary (default: scripts/opencode_trace_local.sh).
    --resume-run-dir DIR      Reuse an existing results/<run_dir> and continue its staged workspace(s).
    --fresh-session-on-resume Start a new session while still using the resume workspace and continuation prompt.
    --stage-full-casestudy-workspace
                              Copy the full source casestudy directory into the runtime workspace.
    --full-prosa              Copy the full Prosa source tree into runtime workspace/prosa.
    --full-prosa-source-dir DIR
                              Full Prosa source tree (default: prosa_v06, override with OPENCODE_FULL_PROSA_SOURCE_DIR).
    --segmented-proof-workflow
                              Enable the segmented proof workflow.
    --skill                   Import workspace-local skills from opencode-trace/.opencode/skill.
    --trace-requests          Save full opencode request traces and copy them into each result directory.
    --no-trace-requests       Disable request tracing even if OPENCODE_TRACE_REQUESTS=1.
    -h, --help                Show this help message.

Account Setup:
    Each account_N/ or account-N/ directory should contain opencode session/auth data.
    Provision them with:
        XDG_DATA_HOME=/path/to/accounts/account_0 opencode account login
        XDG_DATA_HOME=/path/to/accounts/account_1 opencode account login
        ...

    Each worker is bound to one account directory for its full lifetime.
    Effective worker count is limited by both --parallel and the number of accounts.

Workspace Names:
    Names are the directory names under datasets_v06/casestudy_v06/, e.g.:
        2009-RTSS-Lemma3
        2007-RTSS-Theorem1
        2003-RTS-Lemma2

Example:
    ./scripts/run_casestudy_opencode_minprosa.sh \
        --accounts-dir /data/opencode-accounts \
        --model copilot/claude-sonnet-4 \
        --parallel 4 \
        --launch-stagger-seconds 4 \
        2009-RTSS-Lemma3 \
        2007-RTSS-Theorem1
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --accounts-dir)
            ACCOUNTS_DIR="$2"
            shift 2
            ;;
        --model)
            MODEL="$2"
            shift 2
            ;;
        --cases-dir)
            CASES_DIR="$2"
            shift 2
            ;;
        --parallel)
            PARALLEL="$2"
            shift 2
            ;;
        --launch-stagger-seconds)
            LAUNCH_STAGGER_SECONDS="$2"
            shift 2
            ;;
        --run-timeout-seconds)
            RUN_TIMEOUT_SECONDS="$2"
            shift 2
            ;;
        --ratelimit-retry-wait-seconds)
            RATELIMIT_RETRY_WAIT_SECONDS="$2"
            shift 2
            ;;
        --max-ratelimit-retries)
            MAX_RATELIMIT_RETRIES="$2"
            shift 2
            ;;
        --opencode-bin)
            OPENCODE_BIN="$2"
            shift 2
            ;;
        --resume-run-dir)
            RESUME_RUN_DIR="$2"
            shift 2
            ;;
        --fresh-session-on-resume)
            FRESH_SESSION_ON_RESUME=1
            shift
            ;;
        --stage-full-casestudy-workspace)
            STAGE_FULL_CASESTUDY_WORKSPACE=1
            shift
            ;;
        --full-prosa)
            FULL_PROSA=1
            shift
            ;;
        --full-prosa-source-dir)
            FULL_PROSA_SOURCE_DIR="$2"
            shift 2
            ;;
        --segmented-proof-workflow)
            SEGMENTED_PROOF_WORKFLOW=1
            shift
            ;;
        --skill)
            ENABLE_SKILL=1
            shift
            ;;
        --trace-requests)
            TRACE_REQUESTS=1
            shift
            ;;
        --no-trace-requests)
            TRACE_REQUESTS=0
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            CASESTUDIES+=("$1")
            shift
            ;;
    esac
done

# Validate
if [[ -z "$ACCOUNTS_DIR" ]]; then
    echo "ERROR: --accounts-dir is required" >&2
    usage
    exit 1
fi

if [[ ! -d "$ACCOUNTS_DIR" ]]; then
    echo "ERROR: accounts directory not found: $ACCOUNTS_DIR" >&2
    exit 1
fi

if [[ ! -d "$CASES_DIR" ]]; then
    echo "ERROR: cases directory not found: $CASES_DIR" >&2
    exit 1
fi

if [[ -n "$RESUME_RUN_DIR" ]] && [[ ! -d "$RESUME_RUN_DIR" ]]; then
    echo "ERROR: resume run directory not found: $RESUME_RUN_DIR" >&2
    exit 1
fi

if [[ "$FULL_PROSA" -eq 1 ]] && [[ ! -d "$FULL_PROSA_SOURCE_DIR" ]]; then
    echo "ERROR: full Prosa source directory not found: $FULL_PROSA_SOURCE_DIR" >&2
    exit 1
fi

ACCOUNTS_DIR="$(cd "$ACCOUNTS_DIR" && pwd -P)"
CASES_DIR="$(cd "$CASES_DIR" && pwd -P)"
if [[ -n "$RESUME_RUN_DIR" ]]; then
    RESUME_RUN_DIR="$(cd "$RESUME_RUN_DIR" && pwd -P)"
fi
if [[ "$FULL_PROSA" -eq 1 ]]; then
    FULL_PROSA_SOURCE_DIR="$(cd "$FULL_PROSA_SOURCE_DIR" && pwd -P)"
fi

if [[ ! "$PARALLEL" =~ ^[0-9]+$ ]] || [[ "$PARALLEL" -lt 1 ]]; then
    echo "ERROR: --parallel must be a positive integer" >&2
    exit 1
fi

if [[ -n "$RESUME_RUN_DIR" ]] && [[ "$PARALLEL" -ne 1 ]]; then
    echo "ERROR: --resume-run-dir requires --parallel 1 to avoid concurrent writes into the same run directory" >&2
    exit 1
fi

if [[ ! "$LAUNCH_STAGGER_SECONDS" =~ ^[0-9]+$ ]]; then
    echo "ERROR: --launch-stagger-seconds must be a non-negative integer" >&2
    exit 1
fi

if [[ ! "$RATELIMIT_RETRY_WAIT_SECONDS" =~ ^[0-9]+$ ]]; then
    echo "ERROR: --ratelimit-retry-wait-seconds must be a non-negative integer" >&2
    exit 1
fi

if [[ ! "$MAX_RATELIMIT_RETRIES" =~ ^[0-9]+$ ]]; then
    echo "ERROR: --max-ratelimit-retries must be a non-negative integer" >&2
    exit 1
fi

if [[ ${#CASESTUDIES[@]} -eq 0 ]]; then
    echo "ERROR: provide at least one casestudy workspace name" >&2
    usage
    exit 1
fi

if [[ ! -x "$PYTHON_BIN" ]]; then
    echo "ERROR: Python executable not found: $PYTHON_BIN" >&2
    exit 1
fi

if [[ ! -f "$RUNNER" ]]; then
    echo "ERROR: serial runner not found: $RUNNER" >&2
    exit 1
fi

if [[ "$OPENCODE_BIN" == */* ]]; then
    if [[ ! -x "$OPENCODE_BIN" ]]; then
        echo "ERROR: opencode binary not executable: $OPENCODE_BIN" >&2
        exit 1
    fi
else
    if ! command -v "$OPENCODE_BIN" >/dev/null 2>&1; then
        echo "ERROR: opencode binary not found in PATH: $OPENCODE_BIN" >&2
        exit 1
    fi
fi

# Discover accounts (sorted: account_0/account-0, account_1/account-1, ...)
ACCOUNTS=()
shopt -s nullglob
ACCOUNT_CANDIDATES=("$ACCOUNTS_DIR"/account_* "$ACCOUNTS_DIR"/account-*)
shopt -u nullglob

if [[ ${#ACCOUNT_CANDIDATES[@]} -gt 0 ]]; then
    mapfile -t ACCOUNTS < <(
        printf '%s\n' "${ACCOUNT_CANDIDATES[@]}" \
            | awk '!seen[$0]++' \
            | sort -V
    )
fi

if [[ ${#ACCOUNTS[@]} -eq 0 ]]; then
    echo "ERROR: no account_*/ or account-*/ directories found under $ACCOUNTS_DIR" >&2
    echo "Create them with: mkdir -p $ACCOUNTS_DIR/account-0 && XDG_DATA_HOME=$ACCOUNTS_DIR/account-0 opencode account login" >&2
    exit 1
fi

NUM_ACCOUNTS=${#ACCOUNTS[@]}
EXPERIMENT_TAG="$(build_experiment_tag)"

if [[ -z "$RESULT_PREFIX" ]]; then
    RESULT_PREFIX="opencode_casestudy_${EXPERIMENT_TAG}"
fi
if [[ -z "$PARALLEL_RESULT_PREFIX" ]]; then
    PARALLEL_RESULT_PREFIX="opencode_parallel_casestudy_${EXPERIMENT_TAG}"
fi

STAMP="$(date +%Y%m%d_%H%M%S)"
LAUNCH_LOG_DIR="$PROJECT_ROOT/results/${PARALLEL_RESULT_PREFIX}_${STAMP}"
mkdir -p "$LAUNCH_LOG_DIR"

echo "=========================================="
echo " OpenCode Parallel Casestudy Runner"
echo "=========================================="
echo "Experiment:  $EXPERIMENT_TAG"
echo "Model:       ${MODEL:-<default>}"
echo "Parallel:    $PARALLEL"
echo "Launch gap:  ${LAUNCH_STAGGER_SECONDS}s"
echo "Timeout:     ${RUN_TIMEOUT_SECONDS}s"
echo "Paper:       $([[ "$STAGE_FULL_CASESTUDY_WORKSPACE" -eq 1 && "$SEGMENTED_PROOF_WORKFLOW" -eq 1 ]] && echo enabled || echo disabled)"
echo "Skill:       $([[ "$ENABLE_SKILL" -eq 1 ]] && echo enabled || echo disabled)"
echo "Req trace:   $([[ "$TRACE_REQUESTS" -eq 1 ]] && echo enabled || echo disabled)"
echo "Prosa mode:  $([[ "$FULL_PROSA" -eq 1 ]] && echo full || echo minimal)"
if [[ "$FULL_PROSA" -eq 1 ]]; then
    echo "Full Prosa:  $FULL_PROSA_SOURCE_DIR"
fi
echo "Rate-limit:  ${RATELIMIT_RETRY_WAIT_SECONDS}s x ${MAX_RATELIMIT_RETRIES} retries"
echo "Accounts:    $NUM_ACCOUNTS (in $ACCOUNTS_DIR)"
echo "Cases dir:   $CASES_DIR"
if [[ -n "$RESUME_RUN_DIR" ]]; then
    echo "Resume dir:  $RESUME_RUN_DIR"
fi
echo "Casestudies: ${CASESTUDIES[*]}"
echo "Result tag:  $RESULT_PREFIX"
echo "Launch log:  $LAUNCH_LOG_DIR"
echo ""

WORKER_COUNT="$PARALLEL"
if [[ ${#CASESTUDIES[@]} -lt $WORKER_COUNT ]]; then
    WORKER_COUNT="${#CASESTUDIES[@]}"
fi
if [[ $NUM_ACCOUNTS -lt $WORKER_COUNT ]]; then
    WORKER_COUNT="$NUM_ACCOUNTS"
fi

declare -a WORKER_ACCOUNTS=()
declare -a WORKER_PIDS=()

cleanup() {
    local status=$?
    local pid

    set +e
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

    return "$status"
}

trap cleanup EXIT INT TERM

is_ratelimit_launch_log() {
    local launch_log="$1"

    grep -qiE \
        'rate.limit|ratelimit|too[ _.:-]*many[ _.:-]*requests|resource[ _.:-]*exhausted|provider is overloaded|429 status code|status code 429' \
        "$launch_log" 2>/dev/null
}

run_worker() {
    local worker_index="$1"
    shift

    local account_dir="${WORKER_ACCOUNTS[$worker_index]}"
    local worker_log="$LAUNCH_LOG_DIR/worker_${worker_index}.log"
    local casestudy_name
    local casestudy_status
    local casestudy_log
    local casestudy_attempt
    local ratelimit_retries
    local worker_status=0

    : >"$worker_log"
    {
        echo "Worker $worker_index using account dir $account_dir"
        echo "Assigned casestudies: $*"
    } >>"$worker_log"

    local cmd_args=()
    if [[ -n "$MODEL" ]]; then
        cmd_args+=(--model "$MODEL")
    fi
    cmd_args+=(--cases-dir "$CASES_DIR")
    cmd_args+=(--run-timeout-seconds "$RUN_TIMEOUT_SECONDS")
    cmd_args+=(--opencode-bin "$OPENCODE_BIN")
    if [[ -n "$RESUME_RUN_DIR" ]]; then
        cmd_args+=(--resume-run-dir "$RESUME_RUN_DIR")
    fi
    if [[ "$FRESH_SESSION_ON_RESUME" -eq 1 ]]; then
        cmd_args+=(--fresh-session-on-resume)
    fi
    if [[ "$STAGE_FULL_CASESTUDY_WORKSPACE" -eq 1 ]]; then
        cmd_args+=(--stage-full-casestudy-workspace)
    fi
    if [[ "$FULL_PROSA" -eq 1 ]]; then
        cmd_args+=(--full-prosa --full-prosa-source-dir "$FULL_PROSA_SOURCE_DIR")
    fi
    if [[ "$SEGMENTED_PROOF_WORKFLOW" -eq 1 ]]; then
        cmd_args+=(--segmented-proof-workflow)
    fi
    if [[ "$ENABLE_SKILL" -eq 1 ]]; then
        cmd_args+=(--skill)
    fi
    if [[ "$TRACE_REQUESTS" -eq 1 ]]; then
        cmd_args+=(--trace-requests)
    fi

    for casestudy_name in "$@"; do
        casestudy_log="$LAUNCH_LOG_DIR/${casestudy_name}.launch.log"
        casestudy_attempt=0
        ratelimit_retries=0

        while true; do
            casestudy_status=0
            ((casestudy_attempt++)) || true

            echo "[start][worker $worker_index][attempt $casestudy_attempt] $casestudy_name"
            (
                cd "$PROJECT_ROOT"
                XDG_DATA_HOME="$account_dir" \
                XDG_STATE_HOME="$account_dir/state" \
                XDG_CACHE_HOME="$account_dir/cache" \
                XDG_CONFIG_HOME="$account_dir/config" \
                OPENCODE_BIN="$OPENCODE_BIN" \
                OPENCODE_RESULT_PREFIX="$RESULT_PREFIX" \
                "$PYTHON_BIN" "$RUNNER" "${cmd_args[@]}" "$casestudy_name"
            ) >"$casestudy_log" 2>&1 || casestudy_status=$?

            if [[ $casestudy_status -eq 0 ]]; then
                echo "[done][worker $worker_index] $casestudy_name"
                break
            fi

            if is_ratelimit_launch_log "$casestudy_log"; then
                ((ratelimit_retries++)) || true
                if [[ $ratelimit_retries -gt $MAX_RATELIMIT_RETRIES ]]; then
                    echo "[fail][worker $worker_index] $casestudy_name rate-limit retries exhausted (${ratelimit_retries}/${MAX_RATELIMIT_RETRIES}); see $casestudy_log" >&2
                    worker_status=1
                    break
                fi

                echo "[ratelimit][worker $worker_index] $casestudy_name waiting ${RATELIMIT_RETRY_WAIT_SECONDS}s before retry ${ratelimit_retries}/${MAX_RATELIMIT_RETRIES}" >&2
                sleep "$RATELIMIT_RETRY_WAIT_SECONDS"
                continue
            fi

            echo "[fail][worker $worker_index] $casestudy_name (see $casestudy_log)" >&2
            worker_status=1
            break
        done
    done

    return $worker_status
}

overall_status=0
for ((worker_index = 0; worker_index < WORKER_COUNT; worker_index++)); do
    WORKER_ACCOUNTS[worker_index]="${ACCOUNTS[$worker_index]}"
done

echo "Workers:     $WORKER_COUNT"
echo ""

for ((worker_index = 0; worker_index < WORKER_COUNT; worker_index++)); do
    assigned_casestudies=()
    for ((cs_index = worker_index; cs_index < ${#CASESTUDIES[@]}; cs_index += WORKER_COUNT)); do
        assigned_casestudies+=("${CASESTUDIES[$cs_index]}")
    done

    if [[ ${#assigned_casestudies[@]} -eq 0 ]]; then
        continue
    fi

    run_worker "$worker_index" "${assigned_casestudies[@]}" &
    WORKER_PIDS+=("$!")
    if [[ "$LAUNCH_STAGGER_SECONDS" -gt 0 ]] && [[ $worker_index -lt $((WORKER_COUNT - 1)) ]]; then
        sleep "$LAUNCH_STAGGER_SECONDS"
    fi
done

for pid in "${WORKER_PIDS[@]}"; do
    if ! wait "$pid"; then
        overall_status=1
    fi
done

echo ""
echo "All workers finished. Launch logs: $LAUNCH_LOG_DIR"
exit $overall_status
