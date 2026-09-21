#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

state_tool="$script_dir/list_validation_state.py"
prepared=$($script_dir/prepare_utility_list_batch.sh)
pointer="$VALIDATION_ROOT/.work/list_snapshots/current.json"
snapshot_id=$(python3 -c \
  'import json,sys; print(json.load(open(sys.argv[1]))["snapshot_id"])' "$pointer")
prepare_evidence=$(python3 -c \
  'import json,sys; print(json.load(open(sys.argv[1]))["prepare_run_evidence"])' "$pointer")

common_src="$VALIDATION_ROOT/certificates/common"
cert_src="$VALIDATION_ROOT/certificates/utility_foundation"
base_sources=(PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
  ListLastCertificate ListRemCertificate)
target_sources=(ListBatch2Certificate ListBatch3Operations \
  ListBatch3Certificate ListBatch3TypeAudit ListBatch3AssumptionAudit \
  ListBatch4Operations ListBatch4Certificate ListBatch4TypeAudit \
  ListBatch4AssumptionAudit ListBatch5Operations ListBatch5Certificate \
  ListBatch5TypeAudit ListBatch5AssumptionAudit)

for module in "${base_sources[@]}" "${target_sources[@]}"; do
  path="$cert_src/$module.v"
  [[ -f "$path" ]] || path="$common_src/$module.v"
  if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
    if [[ "$module" != PropSPropFoundation ]]; then
      echo "forbidden certificate proof escape in $path" >&2
      exit 1
    fi
  fi
done
foundation_axioms=$(rg -n '^Axiom ' "$common_src/PropSPropFoundation.v" || true)
if [[ "$foundation_axioms" != *"Axiom interpret_strict"* ]] || \
   [[ $(printf '%s\n' "$foundation_axioms" | sed '/^$/d' | wc -l | tr -d ' ') != 1 ]]; then
  echo "Prop/SProp foundation axiom boundary changed" >&2
  exit 1
fi

base_key=$(python3 - "$snapshot_id" "$common_src" "$cert_src" <<'PY'
import hashlib, json, sys
from pathlib import Path
sid, common, cert = sys.argv[1:]
names = ["PropSPropFoundation", "LogicalRelation",
         "SubadditivityNatCorrespondence", "ListLastCertificate",
         "ListRemCertificate"]
items = {"snapshot_id": sid, "sources": {}}
for name in names:
    path = Path(common, name + ".v")
    if not path.exists():
        path = Path(cert, name + ".v")
    items["sources"][name] = hashlib.sha256(path.read_bytes()).hexdigest()
print(hashlib.sha256(json.dumps(items, sort_keys=True).encode()).hexdigest())
PY
)
base_root="$VALIDATION_ROOT/.work/list_check_bases/$base_key"
base_mode=VERIFIED_CACHE
if [[ -d "$base_root" ]]; then
  python3 - "$base_root" "$base_key" <<'PY'
import hashlib, json, sys
from pathlib import Path
root, key = Path(sys.argv[1]), sys.argv[2]
manifest = root / "base_manifest.json"
if not manifest.is_file():
    raise SystemExit("LIST_CHECK_BASE_MANIFEST_MISSING")
data = json.loads(manifest.read_text())
if data.get("base_key") != key:
    raise SystemExit("LIST_CHECK_BASE_KEY_MISMATCH")
for rel, expected in data.get("outputs", {}).items():
    path = root / rel
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise SystemExit("LIST_CHECK_BASE_CORRUPT:" + rel)
PY
else
  base_mode=FRESH
  base_work=$(validation_fresh_workdir utility_list_check_base)
  mkdir -p "$base_work/source/util" "$base_work/imported" "$base_work/certificates"
  cp "$prepared/source/GeneratedListLastSource.v" \
    "$prepared/source/GeneratedListLastSource.vo" "$base_work/source/"
  cp "$prepared/source/util/tactics.v" "$prepared/source/util/tactics.vo" \
    "$prepared/source/util/supremum.v" "$prepared/source/util/supremum.vo" \
    "$base_work/source/util/"
  cp "$prepared/imported/ImportedSubadditivity.vo" \
    "$prepared/imported/ImportedListLast.vo" "$base_work/imported/"
  for module in "${base_sources[@]}"; do
    path="$cert_src/$module.v"
    [[ -f "$path" ]] || path="$common_src/$module.v"
    cp "$path" "$base_work/certificates/"
    (cd "$base_work/certificates" && validation_rocq_compile "$base_work" "$module.v") \
      > "$base_work/certificates/rocq_${module}.log" 2>&1
  done
  mkdir -p "$(dirname "$base_root")"
  mv "$base_work" "$base_root"
  python3 - "$base_root" "$base_key" <<'PY'
import hashlib, json, sys
from pathlib import Path
root, key = Path(sys.argv[1]), sys.argv[2]
outputs = {}
for path in sorted((root / "certificates").glob("*.vo")):
    outputs[path.relative_to(root).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
if len(outputs) != 5:
    raise SystemExit("LIST_CHECK_BASE_OUTPUT_COVERAGE_MISMATCH")
(root / "base_manifest.json").write_text(json.dumps({
    "base_key": key, "outputs": outputs
}, indent=2, sort_keys=True) + "\n")
PY
fi

work=$(validation_fresh_workdir utility_list_check)
mkdir -p "$work/source/util" "$work/imported" "$work/certificates"
cp "$prepared/source/GeneratedListLastSource.v" \
  "$prepared/source/GeneratedListLastSource.vo" "$work/source/"
cp "$prepared/source/util/tactics.v" "$prepared/source/util/tactics.vo" \
  "$prepared/source/util/supremum.v" "$prepared/source/util/supremum.vo" \
  "$work/source/util/"
cp "$prepared/imported/ImportedSubadditivity.vo" \
  "$prepared/imported/ImportedListLast.vo" "$work/imported/"
cp "$base_root/certificates/"*.v "$base_root/certificates/"*.vo \
  "$work/certificates/"
for module in "${target_sources[@]}"; do
  cp "$cert_src/$module.v" "$work/certificates/"
done

log_root="$VALIDATION_ROOT/logs/utility_foundation_expansion/list_batch"
run_stamp=$(TZ=Asia/Hong_Kong date '+%Y%m%d_%H%M%S_HKT')
run_log="$log_root/check_${run_stamp}_${snapshot_id:0:12}"
mkdir -p "$run_log"
events="$run_log/stage_events.jsonl"
: > "$events"
now_ns() { python3 -c 'import time; print(time.time_ns())'; }

start=$(now_ns)
for module in "${target_sources[@]}"; do
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$run_log/rocq_${module}.log" 2>&1
done
end=$(now_ns)
python3 "$state_tool" record --output "$events" --stage certificate_compile \
  --mode FRESH --executed true --start-ns "$start" --end-ns "$end"

start=$(now_ns)
cp "$run_log/rocq_ListBatch5AssumptionAudit.log" "$run_log/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$cert_src/list_batch5_assumption_config.json" \
  --log "$run_log/assumptions.log" \
  --output "$run_log/assumption_summary.json" \
  > "$run_log/assumption_classifier.log"
end=$(now_ns)
python3 "$state_tool" record --output "$events" --stage audit \
  --mode FRESH --executed true --start-ns "$start" --end-ns "$end"

python3 "$state_tool" finish-run --events "$events" \
  --snapshot-id "$snapshot_id" --run-mode CHECK --output "$run_log/stage_evidence.json"
python3 - "$VALIDATION_ROOT/.work/list_checks/current.json" "$snapshot_id" \
  "$prepared" "$prepare_evidence" "$work" "$run_log" "$base_mode" <<'PY'
import json, sys
from pathlib import Path
out, sid, prepared, pe, work, log, base_mode = sys.argv[1:]
path = Path(out)
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(json.dumps({
    "snapshot_id": sid,
    "prepared_root": prepared,
    "prepare_run_evidence": pe,
    "check_work": work,
    "check_log": log,
    "certificate_base_mode": base_mode,
}, indent=2, sort_keys=True) + "\n")
PY
printf '%s\n' "$work"
