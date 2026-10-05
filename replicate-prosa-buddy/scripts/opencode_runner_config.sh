#!/usr/bin/env bash

OPENCODE_RUNNER_CONFIG_SH_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

opencode_config_bool_true() {
    case "${1:-}" in
        1|true|TRUE|yes|YES|on|ON) return 0 ;;
        *) return 1 ;;
    esac
}

opencode_config_file() {
    if [[ -n "${OPENCODE_RUN_CONFIG:-}" ]]; then
        printf '%s\n' "$OPENCODE_RUN_CONFIG"
        return 0
    fi

    local default_config="$PROJECT_ROOT/scripts/opencode_runner_config.env"
    local alias_config="$PROJECT_ROOT/scripts/config.env"
    if [[ -f "$default_config" ]]; then
        printf '%s\n' "$default_config"
    else
        printf '%s\n' "$alias_config"
    fi
}

opencode_config_load() {
    local config_file
    config_file="$(opencode_config_file)"

    if [[ -f "$config_file" ]]; then
        set -a
        # shellcheck source=/dev/null
        source "$config_file"
        set +a
    fi

    OPENCODE_RUN_CONFIG_RESOLVED="$config_file"

    : "${OPENCODE_RUN_NOHUP:=0}"
    : "${OPENCODE_ENABLE_SKILL:=0}"
    : "${OPENCODE_WITH_PAPER:=1}"
    : "${OPENCODE_FULL_PROSA:=0}"
    : "${OPENCODE_RESULTS_ROOT:=$PROJECT_ROOT/results}"
    : "${OPENCODE_NOHUP_LOG_DIR:=$OPENCODE_RESULTS_ROOT/nohup}"
    : "${OPENCODE_RUN_STATE_DIR:=$OPENCODE_NOHUP_LOG_DIR/.runs}"
    : "${OPENCODE_RUN_HEARTBEAT_SECONDS:=30}"
    : "${OPENCODE_MIN_PROSA_SOURCE_DIR:=/home/junyi/prosabuddy/prosaworkspace}"
    : "${OPENCODE_FULL_PROSA_SOURCE_DIR:=/home/junyi/prosabuddy/prosaworkspace}"
    : "${OPENCODE_DIRECT_PROSABUDDY:=1}"
    : "${OPENCODE_CONFIG_DIR:=/home/junyi/prosabuddy/.opencode}"
    if ! opencode_config_bool_true "$OPENCODE_DIRECT_PROSABUDDY"; then
        : "${OPENCODE_MODEL:=github-copilot/gpt-5.4}"
    fi
    : "${OPENCODE_OUR_DIRECT_PROSA_PROBE:=1}"
    : "${OPENCODE_OUR_DIRECT_PROSA_AGENT:=whole-lemma}"
    : "${OPENCODE_OUR_DIRECT_PROSA_PROBE_STEPS:=50}"
    : "${OPENCODE_OUR_DIRECT_PROSA_PROBE_TIMEOUT_SECONDS:=1800}"

    export OPENCODE_MODEL
    export OPENCODE_RUN_CONFIG_RESOLVED
    export OPENCODE_RUN_NOHUP
    export OPENCODE_ENABLE_SKILL
    export OPENCODE_WITH_PAPER
    export OPENCODE_FULL_PROSA
    export OPENCODE_RESULTS_ROOT
    export OPENCODE_NOHUP_LOG_DIR
    export OPENCODE_RUN_STATE_DIR
    export OPENCODE_RUN_HEARTBEAT_SECONDS
    export OPENCODE_MIN_PROSA_SOURCE_DIR
    export OPENCODE_FULL_PROSA_SOURCE_DIR
    export OPENCODE_DIRECT_PROSABUDDY
    export OPENCODE_CONFIG_DIR
    export OPENCODE_OUR_DIRECT_PROSA_PROBE
    export OPENCODE_OUR_DIRECT_PROSA_AGENT
    export OPENCODE_OUR_DIRECT_PROSA_PROBE_STEPS
    export OPENCODE_OUR_DIRECT_PROSA_PROBE_TIMEOUT_SECONDS
}

opencode_config_should_skip_nohup() {
    local arg
    for arg in "$@"; do
        case "$arg" in
            -h|--help|--check|--dry-run|--list-accounts) return 0 ;;
        esac
    done
    return 1
}

opencode_config_maybe_nohup() {
    local script_path="$1"
    shift

    if ! opencode_config_bool_true "${OPENCODE_RUN_NOHUP:-0}"; then
        return 0
    fi
    if [[ "${OPENCODE_NOHUP_CHILD:-0}" == "1" ]]; then
        return 0
    fi
    if opencode_config_should_skip_nohup "$@"; then
        return 0
    fi

    local lifecycle_python
    lifecycle_python="${PYTHON_BIN:-}"
    if [[ -z "$lifecycle_python" ]]; then
        lifecycle_python="$(command -v python3)"
    fi
    if [[ -z "$lifecycle_python" || ! -x "$lifecycle_python" ]]; then
        echo "ERROR: python3 is required for detached runner lifecycle management" >&2
        exit 1
    fi

    "$lifecycle_python" \
        "$OPENCODE_RUNNER_CONFIG_SH_DIR/opencode_runner_config.py" \
        detach-shell "$PROJECT_ROOT" "$script_path" "$@"
    exit "$?"
}
