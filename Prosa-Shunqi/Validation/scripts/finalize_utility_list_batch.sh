#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

state_tool="$script_dir/list_validation_state.py"
common_src="$VALIDATION_ROOT/certificates/common"
cert_src="$VALIDATION_ROOT/certificates/utility_foundation"
fixture_dir="$VALIDATION_ROOT/fixtures/utility_foundation"
cluster_dir="$VALIDATION_ROOT/logs/utility_foundation_expansion/cluster_results"
publish_dir="$VALIDATION_ROOT/imported/utility_foundation"
log_root="$VALIDATION_ROOT/logs/utility_foundation_expansion/list_batch"
mkdir -p "$cluster_dir" "$publish_dir" "$log_root"

prepared=$($script_dir/prepare_utility_list_batch.sh)
pointer="$VALIDATION_ROOT/.work/list_snapshots/current.json"
snapshot_id=$(python3 -c \
  'import json,sys; print(json.load(open(sys.argv[1]))["snapshot_id"])' "$pointer")
prepare_evidence=$(python3 -c \
  'import json,sys; print(json.load(open(sys.argv[1]))["prepare_run_evidence"])' "$pointer")
prepare_mode=$(python3 -c \
  'import json,sys; print(json.load(open(sys.argv[1]))["prepare_mode"])' "$pointer")
prepare_manifest="$prepared/prepare_manifest.json"

run_stamp=$(TZ=Asia/Hong_Kong date '+%Y%m%d_%H%M%S_HKT')
run_log="$log_root/finalize_${run_stamp}_${snapshot_id:0:12}"
mkdir -p "$run_log"
events="$run_log/stage_events.jsonl"
python3 - "$prepare_evidence" "$events" <<'PY'
import json, sys
from pathlib import Path
evidence = json.loads(Path(sys.argv[1]).read_text())
required = {"lean_build", "source_acquisition", "export", "rocq_import"}
stages = evidence.get("stages", [])
if {stage.get("stage") for stage in stages} != required:
    raise SystemExit("FINALIZE_PREPARE_EVIDENCE_INCOMPLETE")
Path(sys.argv[2]).write_text(
    "".join(json.dumps(stage, sort_keys=True) + "\n" for stage in stages)
)
PY

python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" \
  --output "$run_log/baseline_before.json" \
  > "$run_log/baseline_before.log"

if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/List.lean"; then
  echo "forbidden production proof escape in Prosa/Util/List.lean" >&2
  exit 1
fi

common_modules=(PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence)
certificate_modules=(ListSimpleCertificate ListLastCertificate ListRemCertificate \
  ListBatch2Certificate ListBatch3Operations ListBatch3Certificate \
  ListBatch4Operations ListBatch4Certificate \
  ListBatch5Operations ListBatch5Certificate \
  ListSimpleAssumptionAudit ListLastTypeAudit ListBatch2TypeAudit \
  ListBatch3TypeAudit ListBatch4TypeAudit ListBatch5TypeAudit \
  ListLastAssumptionAudit \
  ListBatch2AssumptionAudit ListBatch3AssumptionAudit \
  ListBatch4AssumptionAudit ListBatch5AssumptionAudit)
for module in "${common_modules[@]}" "${certificate_modules[@]}"; do
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

work=$(validation_fresh_workdir utility_list_finalize)
mkdir -p "$work/olean" "$work/source" "$work/imported" "$work/certificates"
cp -R "$prepared/olean/." "$work/olean/"
cp -R "$prepared/source/." "$work/source/"
cp -R "$prepared/imported/." "$work/imported/"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$run_log/final_workdir.txt"

python3 - \
  "$fixture_dir/list_simple_axiom_config.json" \
  "$fixture_dir/list_last_axiom_config.json" \
  "$fixture_dir/list_batch2_axiom_config.json" \
  "$fixture_dir/list_batch3_axiom_config.json" \
  "$fixture_dir/list_batch4_axiom_config.json" \
  "$fixture_dir/list_batch5_axiom_config.json" \
  "$run_log/combined_lean_axiom_config.json" <<'PY'
import json, sys
from pathlib import Path
out = {"declarations": {}}
for name in sys.argv[1:-1]:
    for declaration, spec in json.loads(Path(name).read_text())["declarations"].items():
        if declaration in out["declarations"]:
            raise SystemExit("duplicate Lean axiom audit target: " + declaration)
        out["declarations"][declaration] = spec
Path(sys.argv[-1]).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
PY

python3 - \
  "$cert_src/list_simple_assumption_config.json" \
  "$cert_src/list_last_assumption_config.json" \
  "$cert_src/list_batch2_assumption_config.json" \
  "$cert_src/list_batch3_assumption_config.json" \
  "$cert_src/list_batch4_assumption_config.json" \
  "$cert_src/list_batch5_assumption_config.json" \
  "$run_log/combined_assumption_config.json" <<'PY'
import json, sys
from pathlib import Path
configs = [json.loads(Path(name).read_text()) for name in sys.argv[1:-1]]
out = {
    "prop_sprop_foundation": sorted(set().union(
        *(set(c.get("prop_sprop_foundation", [])) for c in configs))),
    "importer_foundation": sorted(set().union(
        *(set(c.get("importer_foundation", [])) for c in configs))),
    "rocq_sprop_uip": sorted(set().union(
        *(set(c.get("rocq_sprop_uip", [])) for c in configs))),
    "certificates": {},
}
for config in configs:
    for key, spec in config["certificates"].items():
        if key in out["certificates"]:
            raise SystemExit("duplicate assumption audit target: " + key)
        out["certificates"][key] = spec
Path(sys.argv[-1]).write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
PY

now_ns() { python3 -c 'import time; print(time.time_ns())'; }
record_stage() {
  python3 "$state_tool" record --output "$events" --stage "$1" \
    --mode FRESH --executed true --start-ns "$2" --end-ns "$3"
}

start=$(now_ns)
for module in "${common_modules[@]}" "${certificate_modules[@]}"; do
  path="$cert_src/$module.v"
  [[ -f "$path" ]] || path="$common_src/$module.v"
  cp "$path" "$work/certificates/"
  (cd "$work/certificates" && validation_rocq_compile "$work" "$module.v") \
    > "$run_log/rocq_${module}.log" 2>&1
done
record_stage certificate_compile "$start" "$(now_ns)"

start=$(now_ns)
{
  lean -DautoImplicit=false "$fixture_dir/LeanListSimpleAudit.lean"
  lean -DautoImplicit=false "$fixture_dir/LeanListLastAudit.lean"
  lean -DautoImplicit=false "$fixture_dir/LeanListMaxAudit.lean"
  lean -DautoImplicit=false "$fixture_dir/LeanListRemAudit.lean"
  lean -DautoImplicit=false "$fixture_dir/LeanListBatch2Audit.lean"
  lean -DautoImplicit=false "$fixture_dir/LeanListBatch3Audit.lean"
  lean -DautoImplicit=false "$fixture_dir/LeanListBatch4Audit.lean"
  lean -DautoImplicit=false "$fixture_dir/LeanListBatch5Audit.lean"
} > "$run_log/lean_freeze_and_axioms.log" 2>&1
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$run_log/combined_lean_axiom_config.json" \
  --log "$run_log/lean_freeze_and_axioms.log" \
  --output "$run_log/lean_axiom_summary.json" \
  > "$run_log/lean_axiom_classifier.log"
{
  cat "$run_log/rocq_ListSimpleAssumptionAudit.log"
  cat "$run_log/rocq_ListLastAssumptionAudit.log"
  cat "$run_log/rocq_ListBatch2AssumptionAudit.log"
  cat "$run_log/rocq_ListBatch3AssumptionAudit.log"
  cat "$run_log/rocq_ListBatch4AssumptionAudit.log"
  cat "$run_log/rocq_ListBatch5AssumptionAudit.log"
} > "$run_log/assumptions.log"
python3 "$script_dir/audit_assumptions.py" \
  --config "$run_log/combined_assumption_config.json" \
  --log "$run_log/assumptions.log" \
  --output "$run_log/assumption_summary.json" \
  > "$run_log/assumption_classifier.log"
python3 "$script_dir/audit_utility_foundation_baseline.py" \
  --project-root "$PROJECT_ROOT" \
  --output "$run_log/baseline_after.json" \
  > "$run_log/baseline_after.log"
record_stage audit "$start" "$(now_ns)"

start=$(now_ns)
publisher_args=(
  --project-root "$PROJECT_ROOT"
  --validation-root "$VALIDATION_ROOT"
  --source-root "$SOURCE_ROOT"
  --exporter-root "$EXPORTER_ROOT"
  --importer-root "$IMPORTER_ROOT"
  --work "$work"
  --freeze-log "$run_log/lean_freeze_and_axioms.log"
  --lean-axioms "$run_log/lean_axiom_summary.json"
  --assumptions "$run_log/assumption_summary.json"
  --baseline "$run_log/baseline_after.json"
  --snapshot-id "$snapshot_id"
  --prepare-manifest "$prepare_manifest"
  --prepare-evidence "$prepare_evidence"
)
python3 "$script_dir/publish_utility_cluster.py" \
  "${publisher_args[@]}" \
  --config "$cert_src/list_simple_cluster_config.json" \
  --output "$cluster_dir/list_simple.json" \
  > "$run_log/publication_simple.log"
python3 "$script_dir/publish_utility_cluster.py" \
  "${publisher_args[@]}" \
  --config "$cert_src/list_last_cluster_config.json" \
  --output "$cluster_dir/list_last.json" \
  > "$run_log/publication_list.log"
python3 "$script_dir/publish_utility_cluster.py" \
  "${publisher_args[@]}" \
  --config "$cert_src/list_batch3_cluster_config.json" \
  --output "$cluster_dir/list_batch3.json" \
  > "$run_log/publication_batch3.log"
python3 "$script_dir/publish_utility_cluster.py" \
  "${publisher_args[@]}" \
  --config "$cert_src/list_batch4_cluster_config.json" \
  --output "$cluster_dir/list_batch4.json" \
  > "$run_log/publication_batch4.log"
python3 "$script_dir/publish_utility_cluster.py" \
  "${publisher_args[@]}" \
  --config "$cert_src/list_batch5_cluster_config.json" \
  --output "$cluster_dir/list_batch5.json" \
  > "$run_log/publication_batch5.log"

for stem in ListSimple ListLast; do
  cp "$work/imported/$stem.out" "$publish_dir/$stem.out"
  cp "$work/imported/Imported$stem.v" "$publish_dir/Imported$stem.v"
  cp "$work/imported/Imported$stem.vo" "$publish_dir/Imported$stem.vo"
done
for module in ListSimpleCertificate ListSimpleAssumptionAudit \
  ListLastCertificate ListRemCertificate ListLastTypeAudit \
  ListLastAssumptionAudit ListBatch2Certificate ListBatch2TypeAudit \
  ListBatch2AssumptionAudit ListBatch3Operations ListBatch3Certificate \
  ListBatch3TypeAudit ListBatch3AssumptionAudit ListBatch4Operations \
  ListBatch4Certificate ListBatch4TypeAudit ListBatch4AssumptionAudit \
  ListBatch5Operations ListBatch5Certificate ListBatch5TypeAudit \
  ListBatch5AssumptionAudit; do
  cp "$work/certificates/$module.vo" "$publish_dir/$module.vo"
done
python3 "$script_dir/generate_utility_foundation_results.py" \
  > "$run_log/aggregate_status_before_evidence_attach.log"
record_stage publication "$start" "$(now_ns)"

final_evidence="$run_log/stage_evidence.json"
python3 "$state_tool" finish-run --events "$events" \
  --snapshot-id "$snapshot_id" \
  --run-mode "FINALIZE_${prepare_mode}" \
  --output "$final_evidence"
python3 "$state_tool" attach-publication \
  --result "$cluster_dir/list_simple.json" \
  --evidence "$final_evidence" --snapshot-id "$snapshot_id"
python3 "$state_tool" attach-publication \
  --result "$cluster_dir/list_last.json" \
  --evidence "$final_evidence" --snapshot-id "$snapshot_id"
python3 "$state_tool" attach-publication \
  --result "$cluster_dir/list_batch3.json" \
  --evidence "$final_evidence" --snapshot-id "$snapshot_id"
python3 "$state_tool" attach-publication \
  --result "$cluster_dir/list_batch4.json" \
  --evidence "$final_evidence" --snapshot-id "$snapshot_id"
python3 "$state_tool" attach-publication \
  --result "$cluster_dir/list_batch5.json" \
  --evidence "$final_evidence" --snapshot-id "$snapshot_id"
python3 "$script_dir/generate_utility_foundation_results.py" \
  > "$run_log/aggregate_status.log"

perl -pi -e 's/[ \t]+$//' "$run_log"/*.log
(cd "$REPO_ROOT" && git diff --check)

python3 - "$VALIDATION_ROOT/.work/list_finalizes/current.json" \
  "$snapshot_id" "$prepared" "$prepare_evidence" "$work" "$run_log" \
  "$final_evidence" <<'PY'
import json, sys
from pathlib import Path
out, sid, prepared, prep, work, log, evidence = sys.argv[1:]
path = Path(out)
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(json.dumps({
    "snapshot_id": sid,
    "prepared_root": prepared,
    "prepare_run_evidence": prep,
    "final_work": work,
    "final_log": log,
    "finalize_run_evidence": evidence,
}, indent=2, sort_keys=True) + "\n")
PY

echo "util/list.v unified regression: 57 / 57 ACCEPTED"
echo "snapshot: $snapshot_id"
echo "final work directory: $work"
