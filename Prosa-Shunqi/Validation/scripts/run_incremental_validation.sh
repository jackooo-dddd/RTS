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
export VALIDATION_RUN_START_NS
VALIDATION_RUN_START_NS=$(python3 -c 'import time; print(time.time_ns())')

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes
source "$script_dir/common/incremental_validation.sh"
source "$hooks"

if [[ ${CLEAN_FULL:-0} == 1 && ${RECOVER_PREPARE:-0} == 1 ]]; then
  echo "CLEAN_FULL and RECOVER_PREPARE are mutually exclusive" >&2
  exit 2
fi

# Cheap failures must be caught before rebuilding the accepted Lean closure.
bash -n "$hooks" "$script_dir/run_incremental_validation.sh"
jq -e . "$config" >/dev/null
[[ -s "$IMPORTER_ROOT/src/Lean.vo" ]] || {
  echo "importer foundation missing" >&2; exit 1;
}
ulimit -s 65520

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
for function_name in validation_prepare_lean_build \
    validation_prepare_source_acquisition validation_prepare_export \
    validation_prepare_rocq_import; do
  function_body=$(declare -f "$function_name") || {
    echo "missing prepare hook: $function_name" >&2; exit 1;
  }
  descriptor_args+=(--binding "prepare_function_${function_name}=$(printf '%s' "$function_body" | shasum -a 256 | awk '{print $1}')")
done
execution_mode=INCREMENTAL
if [[ ${CLEAN_FULL:-0} == 1 || ${RECOVER_PREPARE:-0} == 1 ]]; then
  execution_mode=CLEAN_FULL
elif [[ ${FILE_VALIDATE:-0} == 1 ]]; then
  execution_mode=FILE_VALIDATE
fi
descriptor_args+=(--binding "execution_mode=$execution_mode")
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

run_or_restore_stage() {
  local events=$1 stage=$2 fingerprint=$3 function_name=$4 work=$5
  local checkpoint="$cache_root/stage_checkpoints/$snapshot_id/$stage/$fingerprint"
  local cross_snapshot=0
  if [[ ${VALIDATION_SPLIT_PREPARE_INPUTS:-0} == 1 && \
        "$stage" != certificate_compile && "$stage" != assumption_audit ]]; then
    checkpoint="$cache_root/stage_checkpoints/by_input/$stage/$fingerprint"
    cross_snapshot=1
  fi
  if [[ ${CLEAN_FULL:-0} != 1 && -d "$checkpoint" ]]; then
    if [[ $cross_snapshot == 1 ]]; then
      python3 "$script_dir/incremental_validation_state.py" restore-stage \
        --prepared "$work" --cache "$checkpoint" --snapshot-id "$snapshot_id" \
        --stage "$stage" --input-fingerprint "$fingerprint" --events "$events" \
        --allow-cross-snapshot
    else
      python3 "$script_dir/incremental_validation_state.py" restore-stage \
        --prepared "$work" --cache "$checkpoint" --snapshot-id "$snapshot_id" \
        --stage "$stage" --input-fingerprint "$fingerprint" --events "$events"
    fi
  else
    run_hook_stage "$events" "$stage" "$fingerprint" "$function_name"
    # A clean run never restores a checkpoint, but each successful stage is
    # sealed so a later explicitly labelled recovery can avoid rebuilding it.
    if [[ ! -e "$checkpoint" ]]; then
      mkdir -p "$(dirname "$checkpoint")"
      python3 "$script_dir/incremental_validation_state.py" seal-stage \
        --prepared "$work" --cache "$checkpoint" --snapshot-id "$snapshot_id" \
        --stage "$stage" --input-fingerprint "$fingerprint"
    fi
  fi
}

prepare_stage_fingerprint() {
  local stage=$1 function_name=$2
  if [[ ${VALIDATION_SPLIT_PREPARE_INPUTS:-0} != 1 ]]; then
    printf '%s\n' "$snapshot_id"
    return
  fi
  local function_hash
  function_hash=$(declare -f "$function_name" | shasum -a 256 | awk '{print $1}')
  python3 "$script_dir/prepare_stage_fingerprint.py" \
    --stage "$stage" --config "$config" --project "$PROJECT_ROOT" \
    --validation "$VALIDATION_ROOT" --source "$SOURCE_ROOT" \
    --exporter "$EXPORTER_ROOT" --importer "$IMPORTER_ROOT" \
    --prepared "$VALIDATION_PREPARED" --function-hash "$function_hash"
}

stage_input_fingerprint() {
  local prior=$1 function_name=$2
  shift 2
  local function_hash
  function_hash=$(declare -f "$function_name" | shasum -a 256 | awk '{print $1}')
  python3 - "$prior" "$function_hash" "$@" <<'PY'
import hashlib, json, sys
from pathlib import Path
prior, function_hash, *names = sys.argv[1:]
items = {"prior": prior, "function_body": function_hash}
for name in names:
    path = Path(name)
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit("stage input missing: " + name)
    items[str(path.resolve())] = hashlib.sha256(path.read_bytes()).hexdigest()
print(hashlib.sha256(json.dumps(items, sort_keys=True).encode()).hexdigest())
PY
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
  export VALIDATION_MODULE_TIMING_FILE="$run_log/module_build_timings.jsonl"
  export VALIDATION_SNAPSHOT_ID="$snapshot_id"
  validation_prepare_lean_path "$work"
  local stage_fp
  stage_fp=$(prepare_stage_fingerprint lean_build validation_prepare_lean_build)
  run_or_restore_stage "$events" lean_build "$stage_fp" \
    validation_prepare_lean_build "$work"
  stage_fp=$(prepare_stage_fingerprint source_acquisition validation_prepare_source_acquisition)
  run_or_restore_stage "$events" source_acquisition "$stage_fp" \
    validation_prepare_source_acquisition "$work"
  stage_fp=$(prepare_stage_fingerprint export validation_prepare_export)
  run_or_restore_stage "$events" export "$stage_fp" \
    validation_prepare_export "$work"
  stage_fp=$(prepare_stage_fingerprint rocq_import validation_prepare_rocq_import)
  run_or_restore_stage "$events" rocq_import "$stage_fp" \
    validation_prepare_rocq_import "$work"
  python3 "$script_dir/incremental_validation_state.py" seal \
    --descriptor "$descriptor" --prepared "$work" --events "$events" \
    > "$run_log/prepare_seal.log"
  if [[ ${CLEAN_FULL:-0} == 1 ]]; then
    prepared="$work"
    local clean_fresh_count
    clean_fresh_count=$(jq -s '[.[] | select(.mode == "FRESH" and .executed == true)] | length' "$events")
    if [[ $clean_fresh_count -eq 4 ]]; then
      mode=CLEAN_FULL
    else
      mode=CLEAN_BUILD_WITH_DECLARED_REUSE
    fi
    if [[ ! -e "$canonical" ]]; then
      cp -R "$work" "$canonical"
      python3 "$script_dir/incremental_validation_state.py" verify \
        --descriptor "$descriptor" --prepared "$canonical" \
        --run-evidence "$run_log/clean_cache_publication_evidence.json" \
        > "$run_log/clean_cache_publication.log"
    fi
  else
    [[ ! -e "$canonical" ]] || {
      echo "prepared cache appeared concurrently: $canonical" >&2; exit 1;
    }
    mv "$work" "$canonical"
    prepared="$canonical"
    local cache_count
    cache_count=$(jq -s '[.[] | select(.mode == "VERIFIED_CACHE")] | length' "$events")
    if [[ $cache_count -eq 0 ]]; then
      mode=FRESH
    elif [[ $cache_count -eq 4 ]]; then
      mode=VERIFIED_CACHE
    else
      mode=MIXED_FRESH_AND_VERIFIED_CACHE
    fi
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

certificate_inputs=("${VALIDATION_CHECK_INPUTS[@]}")
audit_inputs=("${VALIDATION_CHECK_INPUTS[@]}")
publication_inputs=("${VALIDATION_CHECK_INPUTS[@]}")
if [[ ${VALIDATION_SPLIT_CHECK_INPUTS:-0} == 1 ]]; then
  certificate_inputs=()
  audit_inputs=()
  publication_inputs=()
  for input in "${VALIDATION_CHECK_INPUTS[@]}"; do
    case "$(basename "$input")" in
      audit_assumptions.py|*assumption_config.json)
        audit_inputs+=("$input") ;;
      publish_*.py)
        publication_inputs+=("$input") ;;
      *) certificate_inputs+=("$input") ;;
    esac
  done
  [[ ${#certificate_inputs[@]} -gt 0 && ${#audit_inputs[@]} -gt 0 && \
     ${#publication_inputs[@]} -gt 0 ]] || {
    echo "incomplete split check-stage input declaration" >&2; exit 1;
  }
fi
certificate_fingerprint=$(stage_input_fingerprint "$snapshot_id" \
  validation_check_certificate_compile "$config" "${certificate_inputs[@]}")
audit_fingerprint=$(stage_input_fingerprint "$certificate_fingerprint" \
  validation_check_assumption_audit "${audit_inputs[@]}")
publication_fingerprint=$(stage_input_fingerprint "$audit_fingerprint" \
  validation_finalize_publication "${publication_inputs[@]}")
events="$run_log/stage_events.jsonl"
python3 - "$prepare_evidence" "$events" <<'PY'
import json, sys
from pathlib import Path
data = json.loads(Path(sys.argv[1]).read_text())
Path(sys.argv[2]).write_text("".join(
    json.dumps(event, sort_keys=True) + "\n" for event in data["stages"]
))
PY

run_or_restore_stage "$events" certificate_compile "$certificate_fingerprint" \
  validation_check_certificate_compile "$work"
run_or_restore_stage "$events" assumption_audit "$audit_fingerprint" \
  validation_check_assumption_audit "$work"

if [[ "$phase" == finalize ]]; then
  run_hook_stage "$events" publication "$publication_fingerprint" \
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
