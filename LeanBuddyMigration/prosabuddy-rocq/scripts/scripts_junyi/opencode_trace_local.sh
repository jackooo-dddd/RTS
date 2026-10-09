#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
OPENCODE_TRACE_DIR="$PROJECT_ROOT/opencode-trace/packages/opencode"
OPENCODE_TRACE_CONFIG_DIR="$PROJECT_ROOT/opencode-trace/.opencode"

if [[ -n "${BUN_BIN:-}" ]]; then
    BUN="$BUN_BIN"
elif command -v bun >/dev/null 2>&1; then
    BUN="$(command -v bun)"
elif [[ -x "$HOME/.bun/bin/bun" ]]; then
    BUN="$HOME/.bun/bin/bun"
else
    echo "ERROR: bun not found; set BUN_BIN or install bun" >&2
    exit 1
fi

if [[ ! -d "$OPENCODE_TRACE_DIR" ]]; then
    echo "ERROR: missing opencode-trace package dir: $OPENCODE_TRACE_DIR" >&2
    exit 1
fi

if [[ -z "${OPENCODE_CONFIG_DIR:-}" && -d "$OPENCODE_TRACE_CONFIG_DIR" ]]; then
    export OPENCODE_CONFIG_DIR="$OPENCODE_TRACE_CONFIG_DIR"
fi

exec "$BUN" run --cwd "$OPENCODE_TRACE_DIR" ./src/index.ts "$@"