#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
OPENCODE_DIR="${OPENCODE_DIR:-/home/junyi/prosabuddy/packages/opencode}"
OPENCODE_CONFIG_DIR_DEFAULT="/home/junyi/prosabuddy/.opencode"

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

if [[ ! -d "$OPENCODE_DIR" ]]; then
    echo "ERROR: missing opencode package dir: $OPENCODE_DIR" >&2
    exit 1
fi

if [[ -z "${OPENCODE_CONFIG_DIR:-}" && -d "$OPENCODE_CONFIG_DIR_DEFAULT" ]]; then
    export OPENCODE_CONFIG_DIR="$OPENCODE_CONFIG_DIR_DEFAULT"
fi

exec "$BUN" run --cwd "$OPENCODE_DIR" ./src/index.ts "$@"