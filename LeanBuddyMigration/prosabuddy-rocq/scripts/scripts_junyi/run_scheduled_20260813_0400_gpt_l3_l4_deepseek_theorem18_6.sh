#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LAUNCH_SCRIPT="$SCRIPT_DIR/run_ecrts_gpt2_deepseek_t6_new2.sh"
RESULTS_ROOT="${OPENCODE_RESULTS_ROOT:-/home/junyi/results_rebuttal}"

EXPECTED_LOCAL_DATE="2026-08-13"
EXPECTED_TIMEZONE="Asia/Hong_Kong"
SCHEDULE_ID="prosabuddy-gpt-l3-l4-deepseek-book18-6-4x-20260813-0400"
CRON_TAG="# $SCHEDULE_ID"
SCHEDULE_DIR="$RESULTS_ROOT/scheduled/$SCHEDULE_ID"
STARTED_MARKER="$SCHEDULE_DIR/started"
LOCK_FILE="$SCHEDULE_DIR/launch.lock"

remove_own_cron_entry() {
  local current next
  current="$(mktemp)"
  next="$(mktemp)"
  crontab -l >"$current" 2>/dev/null || true
  grep -Fv "$CRON_TAG" "$current" >"$next" || true
  crontab "$next"
  rm -f "$current" "$next"
}

if [[ "$(date +%F)" != "$EXPECTED_LOCAL_DATE" ]]; then
  echo "ERROR: refusing launch outside $EXPECTED_LOCAL_DATE $EXPECTED_TIMEZONE (current: $(date --iso-8601=seconds))" >&2
  exit 3
fi
if [[ "$(date +%Z)" != "HKT" ]] && \
   [[ "$(timedatectl show -p Timezone --value 2>/dev/null || true)" != "$EXPECTED_TIMEZONE" ]]; then
  echo "ERROR: expected timezone $EXPECTED_TIMEZONE, current timezone is $(date +%Z)" >&2
  exit 4
fi

env \
  OPENCODE_DEEPSEEK_CASE_NAME=2015-book-Theorem18_6 \
  OPENCODE_DEEPSEEK_WORKER_TAG=deepseek_book18_6 \
  OPENCODE_SUPERVISOR_TAG=gpt_l3_l4_deepseek_book18_6_4x \
  "$LAUNCH_SCRIPT" --check

mkdir -p "$SCHEDULE_DIR"
exec 9>"$LOCK_FILE"
if ! flock -n 9; then
  echo "Another scheduled launcher instance is active; exiting."
  exit 0
fi
if [[ -e "$STARTED_MARKER" ]]; then
  echo "Scheduled experiment was already launched at $(<"$STARTED_MARKER"); exiting."
  remove_own_cron_entry || true
  exit 0
fi

date --iso-8601=seconds >"$STARTED_MARKER"
remove_own_cron_entry || echo "WARNING: could not remove completed one-time cron entry" >&2

exec env \
  OPENCODE_DEEPSEEK_CASE_NAME=2015-book-Theorem18_6 \
  OPENCODE_DEEPSEEK_WORKER_TAG=deepseek_book18_6 \
  OPENCODE_SUPERVISOR_TAG=gpt_l3_l4_deepseek_book18_6_4x \
  "$LAUNCH_SCRIPT"
