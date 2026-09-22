#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: $0 prepare|check|finalize --name NAME --config FILE --hooks FILE" >&2
  exit 2
}

phase=${1:-}
[[ "$phase" == prepare || "$phase" == check || "$phase" == finalize ]] || usage
shift
name=
config=
hooks=
while [[ $# -gt 0 ]]; do
  case "$1" in
    --name) name=$2; shift 2 ;;
    --config) config=$2; shift 2 ;;
    --hooks) hooks=$2; shift 2 ;;
    *) usage ;;
  esac
done
[[ -n "$name" && -n "$config" && -n "$hooks" ]] || usage
[[ "$name" =~ ^[a-z0-9_]+$ ]]

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes
source "$script_dir/common/incremental_validation.sh"
source "$hooks"

declare -p VALIDATION_PREPARE_INPUTS >/dev/null 2>&1 || VALIDATION_PREPARE_INPUTS=()
declare -p VALIDATION_CHECK_INPUTS >/dev/null 2>&1 || VALIDATION_CHECK_INPUTS=()

cache_root="$VALIDATION_ROOT/.work/incremental/$name"
log_root="$VALIDATION_ROOT/logs/incremental/$name"
mkdir -p "$cache_root/descriptors" "$log_root"
descriptor_tmp="$cache_root/descriptor.$$.json"

descriptor_args=(
  descriptor --config "$config"
  --root "project=$PROJECT_ROOT"
  --root "validation=$VALIDATION_ROOT"
  --root "source=$SOURCE_ROOT"
  --root "exporter=$EXPORTER_ROOT"
  --root "importer=$IMPORTER_ROOT"
  --binding "validation_name=$name"
  --binding "rocq_switch=$ROCQ_SWITCH"
)
for input in "${VALIDATION_PREPARE_INPUTS[@]}"; do
  [[ -s "$input" ]] || { echo "prepare input missing: $input" >&2; exit 1; }
  descriptor_args+=(--binding "prepare_input_$(basename "$input")=$(validation_sha256 "$input")")
done
descriptor_args+=(--output "$descriptor_tmp")
snapshot_id=$(python3 "$script_dir/incremental_validation_state.py" "${descriptor_args[@]}")
descriptor="$cache_root/descriptors/$snapshot_id.json"
if [[ -f "$descriptor" ]]; then
  cmp -s "$descriptor_tmp" "$descriptor" || {
    echo "snapshot descriptor collision" >&2; exit 1;
  }
  rm "$descriptor_tmp"
else
  mv "$descriptor_tmp" "$descriptor"
fi

run_stamp=$(TZ=Asia/Hong_Kong date '+%Y%m%d_%H%M%S_%z')
run_log="$log_root/${phase}_${run_stamp}_${snapshot_id:0:12}"
mkdir -p "$run_log"
canonical="$cache_root/$snapshot_id"
pointer="$cache_root/current.json"

write_pointer() {
  local prepared=$1 evidence=$2 mode=$3
  python3 - "$pointer" "$snapshot_id" "$prepared" "$evidence" "$mode" <<'PY'
import json, sys
from pathlib import Path
out, sid, prepared, evidence, mode = sys.argv[1:]
Path(out).write_text(json.dumps({
    "snapshot_id": sid,
    "prepared_root": prepared,
    "prepare_run_evidence": evidence,
    "prepare_mode": mode,
}, indent=2, sort_keys=True) + "\n")
PY
}

run_hook_stage() {
  local events=$1 stage=$2 fingerprint=$3 function_name=$4
  shift 4
  local start end code state_file
  start=$(validation_now_ns)
  state_file="$VALIDATION_RUN_LOG/${stage}.hook.state"
  set +e
  (
    set -e
    VALIDATION_STAGE_OUTPUTS=()
    VALIDATION_STAGE_MODE=FRESH
    VALIDATION_STAGE_EXECUTED=true
    "$function_name" "$@"
    declare -p VALIDATION_STAGE_OUTPUTS VALIDATION_STAGE_MODE \
      VALIDATION_STAGE_EXECUTED > "$state_file"
  ) > "$VALIDATION_RUN_LOG/${stage}.hook.log" 2>&1
  code=$?
  set -e
  end=$(validation_now_ns)
  if [[ $code -ne 0 ]]; then
    validation_record_failed_stage "$events" "$stage" "$start" "$end" \
      "$fingerprint" "hook $function_name exited $code"
    return "$code"
  fi
  [[ -s "$state_file" ]] || {
    validation_record_failed_stage "$events" "$stage" "$start" "$end" \
      "$fingerprint" "hook $function_name omitted stage state"
    return 1
  }
  source "$state_file"
  validation_record_stage "$events" "$stage" "$VALIDATION_STAGE_MODE" \
    "$VALIDATION_STAGE_EXECUTED" "$start" "$end" "$fingerprint" \
    "${VALIDATION_STAGE_OUTPUTS[@]}"
}

prepare_snapshot() {
  local evidence="$run_log/prepare_stage_evidence.json"
  if [[ ${CLEAN_FULL:-0} != 1 && -d "$canonical" ]]; then
    python3 "$script_dir/incremental_validation_state.py" verify \
      --descriptor "$descriptor" --prepared "$canonical" \
      --run-evidence "$evidence" > "$run_log/prepare_verify.log"
    write_pointer "$canonical" "$evidence" VERIFIED_CACHE
    printf '%s\n' "$canonical"
    return
  fi

  local work events
  work=$(validation_fresh_workdir "incremental_${name}_prepare")
  mkdir -p "$work/olean" "$work/source" "$work/imported"
  events="$run_log/prepare_stage_events.jsonl"
  : > "$events"
  export VALIDATION_PREPARED="$work"
  export VALIDATION_RUN_LOG="$run_log"
  export VALIDATION_SNAPSHOT_ID="$snapshot_id"
  validation_prepare_lean_path "$work"
  run_hook_stage "$events" lean_build "$snapshot_id" validation_prepare_lean_build
  run_hook_stage "$events" source_acquisition "$snapshot_id" validation_prepare_source_acquisition
  run_hook_stage "$events" export "$snapshot_id" validation_prepare_export
  run_hook_stage "$events" rocq_import "$snapshot_id" validation_prepare_rocq_import
  python3 "$script_dir/incremental_validation_state.py" seal \
    --descriptor "$descriptor" --prepared "$work" --events "$events" \
    > "$run_log/prepare_seal.log"
  if [[ ${CLEAN_FULL:-0} == 1 ]]; then
    prepared="$work"
    mode=CLEAN_FULL
  else
    [[ ! -e "$canonical" ]] || {
      echo "prepared cache appeared concurrently: $canonical" >&2; exit 1;
    }
    mv "$work" "$canonical"
    prepared="$canonical"
    mode=FRESH
  fi
  validation_finish_incremental_run "$events" "$snapshot_id" "$mode" "$evidence"
  write_pointer "$prepared" "$evidence" "$mode"
  printf '%s\n' "$prepared"
}

prepared=$(prepare_snapshot)
if [[ "$phase" == prepare ]]; then
  printf '%s\n' "$prepared"
  exit 0
fi

prepare_evidence=$(python3 -c \
  'import json,sys; print(json.load(open(sys.argv[1]))["prepare_run_evidence"])' "$pointer")
work=$(validation_fresh_workdir "incremental_${name}_${phase}")
mkdir -p "$work/olean" "$work/source" "$work/imported" "$work/certificates"
export VALIDATION_PREPARED="$prepared"
export VALIDATION_PHASE_WORK="$work"
export VALIDATION_RUN_LOG="$run_log"
export VALIDATION_SNAPSHOT_ID="$snapshot_id"
export VALIDATION_PREPARE_EVIDENCE="$prepare_evidence"
validation_prepare_lean_path "$work"
validation_check_setup

check_fingerprint=$(python3 - "$snapshot_id" "$config" "$hooks" \
  "${VALIDATION_CHECK_INPUTS[@]}" <<'PY'
import hashlib, json, sys
from pathlib import Path
sid, *names = sys.argv[1:]
items = {"snapshot_id": sid}
for name in names:
    path = Path(name)
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit("check input missing: " + name)
    items[str(path.resolve())] = hashlib.sha256(path.read_bytes()).hexdigest()
print(hashlib.sha256(json.dumps(items, sort_keys=True).encode()).hexdigest())
PY
)
events="$run_log/stage_events.jsonl"
python3 - "$prepare_evidence" "$events" <<'PY'
import json, sys
from pathlib import Path
data = json.loads(Path(sys.argv[1]).read_text())
Path(sys.argv[2]).write_text("".join(
    json.dumps(event, sort_keys=True) + "\n" for event in data["stages"]
))
PY

run_hook_stage "$events" certificate_compile "$check_fingerprint" \
  validation_check_certificate_compile
run_hook_stage "$events" assumption_audit "$check_fingerprint" \
  validation_check_assumption_audit

if [[ "$phase" == finalize ]]; then
  run_hook_stage "$events" publication "$check_fingerprint" \
    validation_finalize_publication
fi
evidence="$run_log/${phase}_stage_evidence.json"
validation_finish_incremental_run "$events" "$snapshot_id" \
  "$(printf '%s' "$phase" | tr '[:lower:]' '[:upper:]')" "$evidence"
python3 - "$cache_root/current_${phase}.json" "$snapshot_id" "$prepared" \
  "$prepare_evidence" "$work" "$run_log" "$evidence" <<'PY'
import json, sys
from pathlib import Path
out, sid, prepared, prep, work, log, evidence = sys.argv[1:]
Path(out).write_text(json.dumps({
    "snapshot_id": sid,
    "prepared_root": prepared,
    "prepare_run_evidence": prep,
    "phase_work": work,
    "run_log": log,
    "phase_evidence": evidence,
}, indent=2, sort_keys=True) + "\n")
PY
printf '%s\n' "$work"
