#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

export DEEPSEEK_2X_SUPERVISOR_TAG="deepseek_2009_rtss_lemma4_2x"
export DEEPSEEK_2X_CASE_NAME="2009-RTSS-Lemma4"
export DEEPSEEK_2X_WORKER_BASE="deepseek_2009_rtss_lemma4"
export DEEPSEEK_2X_MAX_TOTAL_TOKENS="${DEEPSEEK_RTSS_LEMMA4_2X_MAX_TOTAL_TOKENS:-20000000}"
export DEEPSEEK_2X_MAX_RETRIES="${DEEPSEEK_RTSS_LEMMA4_2X_MAX_RETRIES:-20}"

exec "$SCRIPT_DIR/run_deepseek_rtss_method1_2x.sh" "$@"
