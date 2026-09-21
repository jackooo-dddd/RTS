#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

fixture_dir="$VALIDATION_ROOT/fixtures/utility_foundation"
config="$fixture_dir/list_batch_snapshot_config.json"
state_tool="$script_dir/list_validation_state.py"
cache_root="$VALIDATION_ROOT/.work/list_snapshots"
descriptor_tmp="$cache_root/descriptor.$$.json"
mkdir -p "$cache_root/descriptors" \
  "$VALIDATION_ROOT/logs/utility_foundation_expansion/list_batch"

snapshot_id=$(python3 "$state_tool" descriptor \
  --project-root "$PROJECT_ROOT" \
  --validation-root "$VALIDATION_ROOT" \
  --source-root "$SOURCE_ROOT" \
  --exporter-root "$EXPORTER_ROOT" \
  --importer-root "$IMPORTER_ROOT" \
  --rocq-switch "$ROCQ_SWITCH" \
  --config "$config" \
  --output "$descriptor_tmp")
descriptor="$cache_root/descriptors/$snapshot_id.json"
if [[ ! -f "$descriptor" ]]; then
  mv "$descriptor_tmp" "$descriptor"
else
  cmp -s "$descriptor_tmp" "$descriptor" || {
    echo "snapshot descriptor collision" >&2
    exit 1
  }
  rm "$descriptor_tmp"
fi

run_stamp=$(TZ=Asia/Hong_Kong date '+%Y%m%d_%H%M%S_HKT')
run_log="$VALIDATION_ROOT/logs/utility_foundation_expansion/list_batch/prepare_${run_stamp}_${snapshot_id:0:12}"
mkdir -p "$run_log"
canonical="$cache_root/$snapshot_id"

write_pointer() {
  local prepared=$1 evidence=$2 mode=$3
  python3 - "$cache_root/current.json" "$snapshot_id" "$prepared" "$evidence" "$mode" <<'PY'
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

if [[ ${CLEAN_FULL:-0} != 1 && -d "$canonical" ]]; then
  evidence="$run_log/stage_evidence.json"
  python3 "$state_tool" verify \
    --descriptor "$descriptor" \
    --prepared "$canonical" \
    --run-evidence "$evidence" \
    > "$run_log/verify.log"
  write_pointer "$canonical" "$evidence" VERIFIED_CACHE
  printf '%s\n' "$canonical"
  exit 0
fi

work=$(validation_fresh_workdir utility_list_prepare)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/utility_foundation" \
  "$work/source/util" "$work/imported"
validation_prepare_lean_path "$work"
events="$run_log/stage_events.jsonl"
: > "$events"

now_ns() { python3 -c 'import time; print(time.time_ns())'; }
record_stage() {
  python3 "$state_tool" record --output "$events" --stage "$1" \
    --mode FRESH --executed true --start-ns "$2" --end-ns "$3"
}

start=$(now_ns)
validation_compile_lean_module "$work" "Prosa/Util/Tactics" \
  > "$run_log/fresh_Tactics.log" 2>&1
validation_compile_lean_module "$work" "Prosa/Util/Supremum" \
  > "$run_log/fresh_Supremum.log" 2>&1
validation_compile_lean_module "$work" "Prosa/Util/List" \
  > "$run_log/fresh_List.log" 2>&1
validation_compile_lean_module "$work" \
  "Validation/fixtures/utility_foundation/ListLastComputationInterface" \
  > "$run_log/fresh_computation_interface.log" 2>&1
record_stage lean_build "$start" "$(now_ns)"

start=$(now_ns)
cp "$SOURCE_ROOT/util/tactics.v" "$work/source/util/tactics.v"
cp "$SOURCE_ROOT/util/supremum.v" "$work/source/util/supremum.v"
(cd "$work/source" && patch -p1 --forward --batch < \
  "$VALIDATION_ROOT/patches/prosa-v06-rocq93-util-tactics.patch") \
  > "$run_log/source_patch_tactics.log" 2>&1
for source in tactics supremum; do
  (cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
    rocq c -R "$work/source" prosa "util/$source.v") \
    > "$run_log/source_${source}_compile.log" 2>&1
done
source_declarations=$(python3 -c \
  'import json,sys; print(",".join(json.load(open(sys.argv[1]))["source_declarations"]))' \
  "$config")
computational=$(python3 -c \
  'import json,sys; print(",".join(json.load(open(sys.argv[1]))["computational_source_declarations"]))' \
  "$config")
python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" \
  --source-file util/list.v \
  --module GeneratedListLastSource \
  --declarations "$source_declarations" \
  --computational "$computational" \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.list \
  --output "$work/source/GeneratedListLastSource.v" \
  --metadata "$work/source/list_last_source_extraction.json" \
  > "$run_log/source_extraction.log"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedListLastSource.v) \
  > "$run_log/generated_source_compile.log" 2>&1
simple_source_declarations=$(python3 -c \
  'import json,sys; print(",".join(json.load(open(sys.argv[1]))["simple_source_declarations"]))' \
  "$config")
simple_computational=$(python3 -c \
  'import json,sys; print(",".join(json.load(open(sys.argv[1]))["simple_computational_source_declarations"]))' \
  "$config")
python3 "$script_dir/extract_v06_semantic_source.py" \
  --source-root "$SOURCE_ROOT" \
  --source-file util/list.v \
  --module GeneratedListSimpleSource \
  --declarations "$simple_source_declarations" \
  --computational "$simple_computational" \
  --elaborated-evidence \
    "$VALIDATION_ROOT/planning/v06_dependency/declaration_type_evidence.json" \
  --qualified-prefix prosa.util.list \
  --output "$work/source/GeneratedListSimpleSource.v" \
  --metadata "$work/source/list_simple_source_extraction.json" \
  > "$run_log/simple_source_extraction.log"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa GeneratedListSimpleSource.v) \
  > "$run_log/generated_simple_source_compile.log" 2>&1
record_stage source_acquisition "$start" "$(now_ns)"

start=$(now_ns)
export LEAN4EXPORT_STATEMENT_ONLY=$(python3 -c \
  'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["statement_only_targets"]))' \
  "$config")
export LEAN4EXPORT_BODY_THEOREMS=$(python3 -c \
  'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["body_theorem_targets"]))' \
  "$config")
export LEAN4EXPORT_NORMALIZE_THEOREM_TYPES=
export LEAN4EXPORT_NORMALIZE_SUBEXPRESSION_HEADS=
export LEAN4EXPORT_NORMALIZE_DEFINITION_BODIES=
export LEAN4EXPORT_DEFINITION_BODY_PROJECTIONS=
targets=()
while IFS= read -r target; do targets+=("$target"); done < <(
  python3 -c 'import json,sys; c=json.load(open(sys.argv[1])); print("\n".join(c["statement_only_targets"]+c["definition_targets"]+c["body_theorem_targets"]))' "$config")
"$EXPORTER_ROOT/.lake/build/bin/lean4export" \
  "Validation.fixtures.utility_foundation.ListLastComputationInterface" -- \
  "${targets[@]}" > "$work/imported/ListLast.out" 2> "$run_log/export.log"
[[ -s "$work/imported/ListLast.out" ]]
simple_targets=()
while IFS= read -r target; do simple_targets+=("$target"); done < <(
  python3 -c 'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["simple_definition_targets"]))' "$config")
LEAN4EXPORT_STATEMENT_ONLY= LEAN4EXPORT_BODY_THEOREMS= \
  "$EXPORTER_ROOT/.lake/build/bin/lean4export" "Prosa.Util.List" -- \
  "${simple_targets[@]}" > "$work/imported/ListSimple.out" \
  2> "$run_log/simple_export.log"
[[ -s "$work/imported/ListSimple.out" ]]
record_stage export "$start" "$(now_ns)"

start=$(now_ns)
cp "$fixture_dir/ImportedListLast.v" "$work/imported/ImportedListLast.v"
cp "$fixture_dir/ImportedListLastTypeProbe.v" \
  "$work/imported/ImportedListLastTypeProbe.v"
cp "$fixture_dir/ImportedListSimple.v" "$work/imported/ImportedListSimple.v"
cp "$fixture_dir/ImportedListSimpleTypeProbe.v" \
  "$work/imported/ImportedListSimpleTypeProbe.v"
accepted_subadd="$VALIDATION_ROOT/imported/foundation_slice_2_closure/ImportedSubadditivity.vo"
[[ $(validation_sha256 "$accepted_subadd") == \
   99c75886226bdedc70ac976893403eb81eb505babce25310de0881cc289594ff ]]
cp "$accepted_subadd" "$work/imported/"
ulimit -s 65520
(cd "$work/imported" && validation_rocq_compile "$work" ImportedListLast.v) \
  > "$run_log/import.log" 2>&1
(cd "$work/imported" && validation_rocq_compile "$work" \
  ImportedListLastTypeProbe.v) \
  > "$run_log/imported_interface.log" 2>&1
(cd "$work/imported" && validation_rocq_compile "$work" ImportedListSimple.v) \
  > "$run_log/simple_import.log" 2>&1
(cd "$work/imported" && validation_rocq_compile "$work" \
  ImportedListSimpleTypeProbe.v) \
  > "$run_log/simple_imported_interface.log" 2>&1
record_stage rocq_import "$start" "$(now_ns)"

python3 "$state_tool" seal --descriptor "$descriptor" --config "$config" \
  --prepared "$work" --events "$events" > "$run_log/seal.log"

if [[ ${CLEAN_FULL:-0} == 1 ]]; then
  prepared="$work"
  run_mode=CLEAN_FULL
else
  if [[ -e "$canonical" ]]; then
    echo "prepared cache appeared concurrently: $canonical" >&2
    exit 1
  fi
  mv "$work" "$canonical"
  prepared="$canonical"
  run_mode=FRESH
fi
evidence="$run_log/stage_evidence.json"
python3 "$state_tool" finish-run --events "$events" \
  --snapshot-id "$snapshot_id" --run-mode "$run_mode" --output "$evidence"
write_pointer "$prepared" "$evidence" "$run_mode"
printf '%s\n' "$prepared"
