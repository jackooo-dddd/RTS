#!/usr/bin/env bash
# Single-theorem ProsaBuddy replication: 2005-ECRTS-Lemma3 with gpt-6-luna via CLIProxyAPI.
#
# Mirrors scripts/run_ecrts_lemma3_rebuttal.sh (the original experiment) with:
#   - one worker instead of two (single theorem run),
#   - model codexproxy/gpt-6-luna, variant/reasoningEffort "max" (as in the original gpt-5.6-luna launcher),
#   - local paths, Rocq 9.0.1 from the opam switch prosa-0.6.
# Runner flags, token budget (80M), retries (8) and timeout (12h) are unchanged.
#
# Usage: scripts/run_lemma3_gpt6luna.sh [CASE_NAME]
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
R="$(cd "$SCRIPT_DIR/.." && pwd)"
CASE_NAME="${1:-2005-ECRTS-Lemma3}"

PYTHON_BIN="${PYTHON_BIN:-/opt/homebrew/bin/python3.13}"
BUN_BIN="$R/.tools/bin/bun"
ROCQ_BIN_DIR="${ROCQ_BIN_DIR:-$(opam var --switch=prosa-0.6 bin)}"
PROXY_ENV="${PROXY_ENV:-$R/gptAPITest/.env}"          # CLIPROXY_BASE_URL + local proxy key
MODEL="${MODEL:-codexproxy/gpt-6-luna}"
MODEL_ID="${MODEL#*/}"
VARIANT="${VARIANT:-max}"
REASONING_EFFORT="${REASONING_EFFORT:-max}"

MAX_TOTAL_TOKENS=80000000
MAX_RETRIES=8
RUN_TIMEOUT_SECONDS="${RUN_TIMEOUT_SECONDS:-43200}"

for required in "$PYTHON_BIN" "$BUN_BIN" "$ROCQ_BIN_DIR/coqc" "$ROCQ_BIN_DIR/coqtop" "$ROCQ_BIN_DIR/rocq" \
                "$SCRIPT_DIR/run_casestudy_our_minprosa.py" "$SCRIPT_DIR/opencode_our_local.sh" "$PROXY_ENV"; do
  [[ -e "$required" ]] || { echo "ERROR: missing $required" >&2; exit 1; }
done
[[ -d "$R/datasets_v06/casestudy_v06/$CASE_NAME" ]] || { echo "ERROR: case not found: $CASE_NAME" >&2; exit 1; }
[[ -f "$R/prosa_v06/classic/util/all.vo" ]] || { echo "ERROR: prosa_v06 is not compiled" >&2; exit 1; }

set -a; source "$PROXY_ENV"; set +a
code="$(curl -s -o /dev/null -w '%{http_code}' -H "Authorization: Bearer $CLIPROXY_API_KEY" "$CLIPROXY_BASE_URL/models" || true)"
[[ "$code" == "200" ]] || { echo "ERROR: CLIProxyAPI not reachable at $CLIPROXY_BASE_URL (HTTP $code)" >&2; exit 1; }

RESULTS_ROOT="$R/results"
STAMP="$(date +%Y%m%d_%H%M%S)"
# Resume mode (as in the original run_ecrts_gpt2_deepseek_t6_resume_plus2.sh):
#   RESUME_RUN_DIR=<results/our_casestudy_...> RESUME_SUPERVISOR_DIR=<results/supervisor/...> scripts/run_lemma3_gpt6luna.sh
# reuses that run's worker XDG dirs and continues it in a fresh OpenCode session.
declare -a RESUME_ARGS=()
if [[ -n "${RESUME_RUN_DIR:-}" ]]; then
  SUPERVISOR_DIR="${RESUME_SUPERVISOR_DIR:?set RESUME_SUPERVISOR_DIR with RESUME_RUN_DIR}"
  RESUME_ARGS=(--resume-run-dir "$RESUME_RUN_DIR" --fresh-session-on-resume)
else
  SUPERVISOR_DIR="$RESULTS_ROOT/supervisor/${CASE_NAME}_${STAMP}"
fi
WORKER_ROOT="$SUPERVISOR_DIR/worker_1"
mkdir -p "$WORKER_ROOT/data/opencode" "$WORKER_ROOT/state/opencode" "$WORKER_ROOT/cache"

# Provider credentials live only in the worker's isolated XDG data dir (like the original auth.json copy).
umask 077
printf '{"codexproxy":{"type":"api","key":"%s"}}\n' "$CLIPROXY_API_KEY" >"$WORKER_ROOT/data/opencode/auth.json"
umask 022

# The original defined `codexproxy` in the runner machine's global OpenCode config; here it is inline.
provider_config="$(printf '{"provider":{"codexproxy":{"npm":"@ai-sdk/openai","name":"codexproxy","options":{"baseURL":"%s"},"models":{"%s":{"name":"%s","variants":{"%s":{"reasoningEffort":"%s"}}}}}}}' \
  "$CLIPROXY_BASE_URL" "$MODEL_ID" "$MODEL_ID" "$VARIANT" "$REASONING_EFFORT")"

{
  echo "case=$CASE_NAME"
  echo "model=$MODEL variant=$VARIANT reasoning_effort=$REASONING_EFFORT"
  echo "max_total_tokens=$MAX_TOTAL_TOKENS max_retries=$MAX_RETRIES run_timeout_seconds=$RUN_TIMEOUT_SECONDS"
  echo "coqc=$ROCQ_BIN_DIR/coqc ($("$ROCQ_BIN_DIR/coqc" --version | head -1))"
  echo "bun=$("$BUN_BIN" --version)"
  echo "started_at=$(date -Iseconds)"
  [[ -n "${RESUME_RUN_DIR:-}" ]] && echo "resume_run_dir=$RESUME_RUN_DIR (fresh session)"
} >>"$SUPERVISOR_DIR/config.txt"
echo "supervisor_dir=$SUPERVISOR_DIR"

exec env -u OPENCODE_MODEL -u OPENCODE_VARIANT -u COQPATH -u ROCQPATH \
  "PATH=$ROCQ_BIN_DIR:$(dirname "$BUN_BIN"):/usr/bin:/bin:/usr/sbin:/sbin:/opt/homebrew/bin" \
  "BUN_BIN=$BUN_BIN" \
  "OPENCODE_DIR=$R/opencode/packages/opencode" \
  "OPENCODE_BIN=$SCRIPT_DIR/opencode_our_local.sh" \
  "OPENCODE_RUN_CONFIG=$SCRIPT_DIR/opencode_runner_config.env" \
  "XDG_DATA_HOME=$WORKER_ROOT/data" \
  "XDG_STATE_HOME=$WORKER_ROOT/state" \
  "XDG_CACHE_HOME=$WORKER_ROOT/cache" \
  "XDG_CONFIG_HOME=$WORKER_ROOT/config" \
  OPENCODE_DISABLE_CLAUDE_CODE=1 \
  OPENCODE_RUN_NOHUP=0 \
  PYTHONUNBUFFERED=1 \
  "OPENCODE_RESULTS_ROOT=$RESULTS_ROOT" \
  "OPENCODE_RESULT_PREFIX=our_casestudy_fullprosa_gpt6luna_run1" \
  "OPENCODE_CONFIG_CONTENT=$provider_config" \
  "$PYTHON_BIN" "$SCRIPT_DIR/run_casestudy_our_minprosa.py" \
    --model "$MODEL" \
    --variant "$VARIANT" \
    --cases-dir "$R/datasets_v06/casestudy_v06" \
    --run-timeout-seconds "$RUN_TIMEOUT_SECONDS" \
    --max-total-tokens "$MAX_TOTAL_TOKENS" \
    --max-retries "$MAX_RETRIES" \
    --opencode-bin "$SCRIPT_DIR/opencode_our_local.sh" \
    --stage-full-casestudy-workspace \
    --full-prosa \
    --full-prosa-source-dir "$R/prosa_v06" \
    --segmented-proof-workflow \
    --skill \
    --trace-requests \
    ${RESUME_ARGS[@]+"${RESUME_ARGS[@]}"} \
    "$CASE_NAME"
