#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SUPPORT_ROOT="$PROJECT_ROOT"
if [[ ! -f "$SUPPORT_ROOT/scripts/opencode_runner_config.sh" ]]; then
	SUPPORT_ROOT="$(cd "$PROJECT_ROOT/.." && pwd)"
fi

source "$SUPPORT_ROOT/scripts/opencode_runner_config.sh"
opencode_config_load
opencode_config_maybe_nohup "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" "$@"

CASES_DIR_DEFAULT="/home/junyi/dataset/Case_Study"
SKILL_SOURCE_DIR_DEFAULT="/home/junyi/prosabuddy/.opencode/skill"

PROSA_SOURCE_DIR_DEFAULT="/home/junyi/prosabuddy/prosaworkspace"
FULL_PROSA_SOURCE_DIR_DEFAULT="/home/junyi/prosabuddy/prosaworkspace"

DEFAULT_PROSA_TAG="minprosa"
if opencode_config_bool_true "${OPENCODE_FULL_PROSA:-0}"; then
	DEFAULT_PROSA_TAG="fullprosa"
fi

export PYTHON_BIN="${PYTHON_BIN:-$(command -v python3)}"
export OPENCODE_BIN="${OPENCODE_BIN:-$SUPPORT_ROOT/scripts/opencode_our_local.sh}"
export OPENCODE_RESULT_PREFIX="${OPENCODE_RESULT_PREFIX:-our_casestudy_${DEFAULT_PROSA_TAG}}"
export OPENCODE_PARALLEL_RESULT_PREFIX="${OPENCODE_PARALLEL_RESULT_PREFIX:-our_parallel_casestudy_${DEFAULT_PROSA_TAG}}"
export OPENCODE_RECORD_RUNNER="${OPENCODE_RECORD_RUNNER:-run_casestudy_our_minprosa.sh}"
export OPENCODE_SERIAL_RUNNER="${OPENCODE_SERIAL_RUNNER:-$PROJECT_ROOT/scripts/run_casestudy_our_minprosa.py}"
export OPENCODE_SKILL_SOURCE_DIR="${OPENCODE_SKILL_SOURCE_DIR:-$SKILL_SOURCE_DIR_DEFAULT}"
export OPENCODE_CASESTUDY_DIR="${OPENCODE_CASESTUDY_DIR:-$CASES_DIR_DEFAULT}"
export OPENCODE_MIN_PROSA_SOURCE_DIR="${OPENCODE_MIN_PROSA_SOURCE_DIR:-$PROSA_SOURCE_DIR_DEFAULT}"
export OPENCODE_FULL_PROSA_SOURCE_DIR="${OPENCODE_FULL_PROSA_SOURCE_DIR:-$FULL_PROSA_SOURCE_DIR_DEFAULT}"

EXTRA_ARGS=()
if opencode_config_bool_true "${OPENCODE_WITH_PAPER:-0}"; then
	EXTRA_ARGS+=(--stage-full-casestudy-workspace --segmented-proof-workflow)
fi
if opencode_config_bool_true "${OPENCODE_ENABLE_SKILL:-0}"; then
	EXTRA_ARGS+=(--skill)
fi

exec "$SUPPORT_ROOT/scripts/run_casestudy_opencode_minprosa.sh" "${EXTRA_ARGS[@]}" "$@"