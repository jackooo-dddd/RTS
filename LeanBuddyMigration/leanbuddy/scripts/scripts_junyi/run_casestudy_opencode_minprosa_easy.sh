#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
source "$PROJECT_ROOT/scripts/opencode_runner_config.sh"
opencode_config_load
opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

RUNNER="$PROJECT_ROOT/scripts/run_casestudy_opencode_minprosa.sh"
SERIAL_RUNNER="${OPENCODE_SERIAL_RUNNER:-$PROJECT_ROOT/scripts/run_casestudy_opencode_minprosa.py}"

DEFAULT_ACCOUNTS_ROOT="${OPENCODE_ACCOUNTS_ROOT:-$HOME/.local/share}"
DEFAULT_PARALLEL="${OPENCODE_PARALLEL:-}"
DEFAULT_STAGGER_SECONDS="${OPENCODE_LAUNCH_STAGGER_SECONDS:-4}"
DEFAULT_TIMEOUT_SECONDS="${OPENCODE_RUN_TIMEOUT_SECONDS:-43200}"
DEFAULT_OPENCODE_BIN="${OPENCODE_BIN:-$PROJECT_ROOT/scripts/opencode_trace_local.sh}"
DEFAULT_CASES_DIR="${OPENCODE_CASESTUDY_DIR:-$PROJECT_ROOT/datasets_v06/casestudy_v06}"
DEFAULT_STAGE_FULL_CASESTUDY_WORKSPACE=0
DEFAULT_FULL_PROSA=0
DEFAULT_FULL_PROSA_SOURCE_DIR="${OPENCODE_FULL_PROSA_SOURCE_DIR:-$PROJECT_ROOT/prosa_v06}"
DEFAULT_SEGMENTED_PROOF_WORKFLOW=0
DEFAULT_ENABLE_SKILL=0
DEFAULT_TRACE_REQUESTS=0
DEFAULT_DIRECT_PROSABUDDY=0
if opencode_config_bool_true "${OPENCODE_WITH_PAPER:-0}"; then
    DEFAULT_STAGE_FULL_CASESTUDY_WORKSPACE=1
    DEFAULT_SEGMENTED_PROOF_WORKFLOW=1
fi
if opencode_config_bool_true "${OPENCODE_FULL_PROSA:-0}"; then
    DEFAULT_FULL_PROSA=1
fi
if opencode_config_bool_true "${OPENCODE_ENABLE_SKILL:-0}"; then
    DEFAULT_ENABLE_SKILL=1
fi
if opencode_config_bool_true "${OPENCODE_TRACE_REQUESTS:-0}"; then
    DEFAULT_TRACE_REQUESTS=1
fi
if opencode_config_bool_true "${OPENCODE_DIRECT_PROSABUDDY:-0}"; then
    DEFAULT_DIRECT_PROSABUDDY=1
fi
if [[ "$DEFAULT_DIRECT_PROSABUDDY" -eq 1 ]]; then
    DEFAULT_MODEL="${OPENCODE_MODEL:-}"
else
    DEFAULT_MODEL="${OPENCODE_MODEL:-github-copilot/gpt-5.4}"
fi

ACCOUNTS_ROOT="$DEFAULT_ACCOUNTS_ROOT"
MODEL="$DEFAULT_MODEL"
MODEL_EXPLICIT=0
PARALLEL="$DEFAULT_PARALLEL"
PYTHON_BIN="${PYTHON_BIN:-$(command -v python3)}"
LAUNCH_STAGGER_SECONDS="$DEFAULT_STAGGER_SECONDS"
RUN_TIMEOUT_SECONDS="$DEFAULT_TIMEOUT_SECONDS"
OPENCODE_BIN="$DEFAULT_OPENCODE_BIN"
CASES_DIR="$DEFAULT_CASES_DIR"
STAGE_FULL_CASESTUDY_WORKSPACE="$DEFAULT_STAGE_FULL_CASESTUDY_WORKSPACE"
FULL_PROSA="$DEFAULT_FULL_PROSA"
FULL_PROSA_SOURCE_DIR="$DEFAULT_FULL_PROSA_SOURCE_DIR"
SEGMENTED_PROOF_WORKFLOW="$DEFAULT_SEGMENTED_PROOF_WORKFLOW"
ENABLE_SKILL="$DEFAULT_ENABLE_SKILL"
TRACE_REQUESTS="$DEFAULT_TRACE_REQUESTS"
DIRECT_PROSABUDDY="$DEFAULT_DIRECT_PROSABUDDY"
LIST_ACCOUNTS=0
DRY_RUN=0
RESUME_RUN_DIR=""
CASESTUDIES=()

usage() {
    cat <<EOF
Usage:
    ./scripts/run_casestudy_opencode_minprosa_easy.sh [OPTIONS] WORKSPACE_NAME [WORKSPACE_NAME ...]

Defaults:
  accounts root:           $DEFAULT_ACCOUNTS_ROOT
    model:                   ${DEFAULT_MODEL:-<prosabuddy config>}
  parallel workers:        auto-detect from account-*/account_*/ count
  launch stagger seconds:  $DEFAULT_STAGGER_SECONDS
  run timeout seconds:     $DEFAULT_TIMEOUT_SECONDS
    direct prosabuddy:       $([[ "$DEFAULT_DIRECT_PROSABUDDY" -eq 1 ]] && echo enabled || echo disabled)
    opencode bin:            $DEFAULT_OPENCODE_BIN
    cases dir:               $DEFAULT_CASES_DIR
    full Prosa source:       $DEFAULT_FULL_PROSA_SOURCE_DIR

Options:
  --accounts-root DIR      Parent directory containing account-0/, account-1/, ...
                           or account_0/, account_1/, ...
    --model MODEL            Provider/model string.
    --cases-dir DIR          Casestudy root directory. Default is datasets_v06/casestudy_v06.
  --parallel N             Worker count. Default is all detected accounts.
  --launch-stagger-seconds N
                           Delay between worker starts.
  --run-timeout-seconds N  Per-casestudy timeout.
    --opencode-bin PATH      opencode binary or wrapper path.
    --direct-prosabuddy      Use the local prosabuddy config directly; no account dirs.
    --account-workers        Use account_*/account-* worker dirs under --accounts-root.
    --resume-run-dir DIR     Reuse an existing results/<run_dir> and continue its staged workspace(s).
    --skill                  Copy workspace-local skills into the staged workspace and enable skill use.
    --stage-full-casestudy-workspace
                                                     Copy the full source casestudy directory into the runtime workspace.
    --full-prosa             Copy the full Prosa source tree into runtime workspace/prosa.
    --full-prosa-source-dir DIR
                                                     Full Prosa source tree. Default is prosa_v06.
    --segmented-proof-workflow
                                                     Enable the segmented proof workflow.
    --trace-requests       Save full opencode request traces in each result directory.
    --no-trace-requests    Disable request tracing even if OPENCODE_TRACE_REQUESTS=1.
  --list-accounts          Show detected accounts and exit.
  --dry-run                Print the final command and exit.
  -h, --help               Show this help message.

Workspace names are the directory names under datasets_v06/casestudy_v06/, e.g.:
    2009-RTSS-Lemma3
    2007-RTSS-Theorem1

Examples:
    ./scripts/run_casestudy_opencode_minprosa_easy.sh 2009-RTSS-Lemma3

    ./scripts/run_casestudy_opencode_minprosa_easy.sh \
        --parallel 3 \
        2009-RTSS-Lemma3 \
        2007-RTSS-Theorem1

Environment overrides:
  OPENCODE_ACCOUNTS_ROOT
  OPENCODE_MODEL
  OPENCODE_PARALLEL
  OPENCODE_LAUNCH_STAGGER_SECONDS
  OPENCODE_RUN_TIMEOUT_SECONDS
    OPENCODE_DIRECT_PROSABUDDY
    OPENCODE_BIN
    OPENCODE_CASESTUDY_DIR
    OPENCODE_FULL_PROSA_SOURCE_DIR
    OPENCODE_TRACE_REQUESTS
EOF
}

detect_accounts() {
    local accounts_root="$1"
    local -n detected_ref="$2"
    local candidates=()

    detected_ref=()
    shopt -s nullglob
    candidates=("$accounts_root"/account-[0-9]* "$accounts_root"/account_[0-9]*)
    shopt -u nullglob

    if [[ ${#candidates[@]} -eq 0 ]]; then
        return 1
    fi

    mapfile -t detected_ref < <(
        printf '%s\n' "${candidates[@]}" \
            | awk '!seen[$0]++' \
            | sort -V
    )
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --accounts-root)
            ACCOUNTS_ROOT="$2"
            shift 2
            ;;
        --model)
            MODEL="$2"
            MODEL_EXPLICIT=1
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
        --opencode-bin)
            OPENCODE_BIN="$2"
            shift 2
            ;;
        --direct-prosabuddy)
            DIRECT_PROSABUDDY=1
            shift
            ;;
        --account-workers)
            DIRECT_PROSABUDDY=0
            shift
            ;;
        --resume-run-dir)
            RESUME_RUN_DIR="$2"
            shift 2
            ;;
        --skill)
            ENABLE_SKILL=1
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
        --trace-requests)
            TRACE_REQUESTS=1
            shift
            ;;
        --no-trace-requests)
            TRACE_REQUESTS=0
            shift
            ;;
        --list-accounts)
            LIST_ACCOUNTS=1
            shift
            ;;
        --dry-run)
            DRY_RUN=1
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

if [[ "$DIRECT_PROSABUDDY" -eq 0 && ! -d "$ACCOUNTS_ROOT" ]]; then
    echo "ERROR: accounts root not found: $ACCOUNTS_ROOT" >&2
    exit 1
fi

if [[ "$DIRECT_PROSABUDDY" -eq 1 && ! -x "$PYTHON_BIN" ]]; then
    echo "ERROR: Python executable not found: $PYTHON_BIN" >&2
    exit 1
fi

if [[ "$DIRECT_PROSABUDDY" -eq 1 && ! -f "$SERIAL_RUNNER" ]]; then
    echo "ERROR: serial runner not found: $SERIAL_RUNNER" >&2
    exit 1
fi

if [[ ! -d "$CASES_DIR" ]]; then
    echo "ERROR: cases dir not found: $CASES_DIR" >&2
    exit 1
fi

if [[ -n "$RESUME_RUN_DIR" ]] && [[ ! -d "$RESUME_RUN_DIR" ]]; then
    echo "ERROR: resume run dir not found: $RESUME_RUN_DIR" >&2
    exit 1
fi

if [[ "$FULL_PROSA" -eq 1 ]] && [[ ! -d "$FULL_PROSA_SOURCE_DIR" ]]; then
    echo "ERROR: full Prosa source dir not found: $FULL_PROSA_SOURCE_DIR" >&2
    exit 1
fi

if [[ "$FULL_PROSA" -eq 1 ]]; then
    FULL_PROSA_SOURCE_DIR="$(cd "$FULL_PROSA_SOURCE_DIR" && pwd -P)"
fi

if [[ -n "$RESUME_RUN_DIR" ]]; then
    RESUME_RUN_DIR="$(cd "$RESUME_RUN_DIR" && pwd -P)"
fi

DETECTED_ACCOUNTS=()
if [[ "$DIRECT_PROSABUDDY" -eq 0 ]] && ! detect_accounts "$ACCOUNTS_ROOT" DETECTED_ACCOUNTS; then
    echo "ERROR: no account-*/ or account_*/ directories found under $ACCOUNTS_ROOT" >&2
    exit 1
fi

if [[ "$LIST_ACCOUNTS" -eq 1 ]]; then
    if [[ "$DIRECT_PROSABUDDY" -eq 1 ]]; then
        echo "Direct prosabuddy mode is enabled; account directories are not used."
        exit 0
    fi
    echo "Detected ${#DETECTED_ACCOUNTS[@]} account directories under $ACCOUNTS_ROOT:"
    printf '  %s\n' "${DETECTED_ACCOUNTS[@]}"
    exit 0
fi

if [[ -z "$PARALLEL" ]]; then
    if [[ "$DIRECT_PROSABUDDY" -eq 1 || -n "$RESUME_RUN_DIR" ]]; then
        PARALLEL=1
    else
        PARALLEL="${#DETECTED_ACCOUNTS[@]}"
    fi
fi

if [[ ! "$PARALLEL" =~ ^[0-9]+$ ]] || [[ "$PARALLEL" -lt 1 ]]; then
    echo "ERROR: --parallel must be a positive integer" >&2
    exit 1
fi

if [[ ${#CASESTUDIES[@]} -eq 0 ]]; then
    echo "ERROR: provide at least one casestudy workspace name" >&2
    usage
    exit 1
fi

if [[ "$DIRECT_PROSABUDDY" -eq 1 ]]; then
    CMD=(
        env
        -u
        OPENCODE_MODEL
        "$PYTHON_BIN"
        "$SERIAL_RUNNER"
        --cases-dir "$CASES_DIR"
        --run-timeout-seconds "$RUN_TIMEOUT_SECONDS"
        --opencode-bin "$OPENCODE_BIN"
    )
    if [[ "$MODEL_EXPLICIT" -eq 1 ]]; then
        CMD+=(--model "$MODEL")
    fi
else
    CMD=(
        "$RUNNER"
        --accounts-dir "$ACCOUNTS_ROOT"
        --model "$MODEL"
        --cases-dir "$CASES_DIR"
        --parallel "$PARALLEL"
        --launch-stagger-seconds "$LAUNCH_STAGGER_SECONDS"
        --run-timeout-seconds "$RUN_TIMEOUT_SECONDS"
        --opencode-bin "$OPENCODE_BIN"
    )
fi

if [[ "$STAGE_FULL_CASESTUDY_WORKSPACE" -eq 1 ]]; then
    CMD+=(--stage-full-casestudy-workspace)
fi

if [[ "$FULL_PROSA" -eq 1 ]]; then
    CMD+=(--full-prosa --full-prosa-source-dir "$FULL_PROSA_SOURCE_DIR")
fi

if [[ "$SEGMENTED_PROOF_WORKFLOW" -eq 1 ]]; then
    CMD+=(--segmented-proof-workflow)
fi

if [[ "$ENABLE_SKILL" -eq 1 ]]; then
    CMD+=(--skill)
fi

if [[ "$TRACE_REQUESTS" -eq 1 ]]; then
    CMD+=(--trace-requests)
fi

if [[ -n "$RESUME_RUN_DIR" ]]; then
    CMD+=(--resume-run-dir "$RESUME_RUN_DIR")
fi

CMD+=("${CASESTUDIES[@]}")

echo "=========================================="
echo " OpenCode Easy Casestudy Runner"
echo "=========================================="
echo "Direct mode:    $([[ "$DIRECT_PROSABUDDY" -eq 1 ]] && echo prosabuddy || echo account-workers)"
if [[ "$DIRECT_PROSABUDDY" -eq 0 ]]; then
    echo "Accounts root:  $ACCOUNTS_ROOT"
    echo "Detected:       ${#DETECTED_ACCOUNTS[@]} account(s)"
fi
echo "Parallel:       $PARALLEL"
echo "Model:          ${MODEL:-<prosabuddy config>}"
echo "Cases dir:      $CASES_DIR"
echo "Timeout:        ${RUN_TIMEOUT_SECONDS}s"
echo "Opencode bin:   $OPENCODE_BIN"
echo "Paper:          $([[ "$STAGE_FULL_CASESTUDY_WORKSPACE" -eq 1 && "$SEGMENTED_PROOF_WORKFLOW" -eq 1 ]] && echo enabled || echo disabled)"
echo "Skill import:   $([[ "$ENABLE_SKILL" -eq 1 ]] && echo enabled || echo disabled)"
echo "Prosa mode:     $([[ "$FULL_PROSA" -eq 1 ]] && echo full || echo minimal)"
if [[ "$FULL_PROSA" -eq 1 ]]; then
    echo "Full Prosa:     $FULL_PROSA_SOURCE_DIR"
fi
echo "Casestudies:    ${CASESTUDIES[*]}"
echo ""

if [[ "$DRY_RUN" -eq 1 ]]; then
    printf 'Command:'
    printf ' %q' "${CMD[@]}"
    printf '\n'
    exit 0
fi

exec "${CMD[@]}"
