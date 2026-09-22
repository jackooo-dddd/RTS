#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
ready_snapshot=0005a8a78597bde2fe967345a971dbafe995f4c5543acd95bc7844d244bceb8b
ready_cache="$VALIDATION_ROOT/.work/incremental/behavior_ready/$ready_snapshot"
ready_prepare="$ready_cache/prepare_manifest.json"
ready_build_manifest="$ready_cache/dependency_build_manifest.json"
ready_status="$pipeline_dir/behavior_ready_module_status.json"
ready_manifest="$pipeline_dir/behavior_ready_module_manifest.json"
fixture="$VALIDATION_ROOT/fixtures/translation_order/BehaviorAllInterface.lean"
axiom_config="$VALIDATION_ROOT/fixtures/translation_order/behavior_all_lean_axiom_config.json"
publish_dir="$VALIDATION_ROOT/imported/translation_order/behavior_all"
run_stamp=$(date '+%Y%m%d_%H%M%S_%z')
log_dir="$VALIDATION_ROOT/logs/translation_order/behavior_all/finalize_$run_stamp"
mkdir -p "$publish_dir" "$log_dir"

jq -e --arg snapshot "$ready_snapshot" '
  .status == "PASS" and
  .coverage.accepted_files == 26 and
  .coverage.accepted_declarations == 247 and
  .coverage.translated_but_not_certified == 0 and
  .per_file["behavior/ready.v"].status == "ACCEPTED_V06_FILE"' \
  "$ready_status" >/dev/null
jq -e --arg snapshot "$ready_snapshot" '
  .acceptance == "ACCEPTED_V06_FILE" and .snapshot_id == $snapshot' \
  "$ready_manifest" >/dev/null

work=$(validation_fresh_workdir behavior_all_finalize)
mkdir -p "$work/olean/Prosa/Behavior" \
  "$work/olean/Validation/fixtures/translation_order" \
  "$work/source/behavior"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

timing_jsonl="$log_dir/stage_timings.jsonl"
: > "$timing_jsonl"
now_ns() { python3 -c 'import time; print(time.time_ns())'; }
record_stage() {
  local stage=$1 start=$2 end=$3 status=$4 mode=$5 executions=$6 hits=$7
  python3 - "$timing_jsonl" "$stage" "$start" "$end" "$status" \
    "$mode" "$executions" "$hits" <<'PY'
import json, sys
path, stage, start, end, status, mode, executions, hits = sys.argv[1:]
record = {
    "stage": stage,
    "status": status,
    "provenance": mode,
    "execution_count": int(executions),
    "cache_hits": int(hits),
    "elapsed_seconds": (int(end) - int(start)) / 1_000_000_000,
}
with open(path, "a") as stream:
    stream.write(json.dumps(record, sort_keys=True) + "\n")
PY
}

# Validate and materialize the sealed Rocq dependency closure, then compile the
# byte-identical authoritative aggregation module.
stage_start=$(now_ns)
[[ $(validation_sha256 "$SOURCE_ROOT/behavior/all.v") == \
  3c54a82734ebc51a75c66ff0c71f2828bfc469f8a9756a00b3a4a7b54fcbfa4d ]]
[[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="behavior/all.v" for r in csv.DictReader(open(sys.argv[1]))))' \
  "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 0 ]]
cp "$SOURCE_ROOT/behavior/all.v" "$work/source/behavior/all.v"
python3 - "$ready_cache" "$ready_prepare" "$work/source" \
  "$work/source_dependency_reuse.json" <<'PY'
import hashlib, json, shutil, sys
from pathlib import Path

cache, manifest_path, destination, evidence_path = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads(manifest_path.read_text())
if manifest.get("snapshot_id") != "0005a8a78597bde2fe967345a971dbafe995f4c5543acd95bc7844d244bceb8b":
    raise SystemExit("READY_CACHE_SNAPSHOT_MISMATCH")
entries = manifest["outputs"]["source_acquisition"]["files"]
copied = {}
for relative, expected in entries.items():
    source = cache / relative
    if not source.is_file() or sha(source) != expected:
        raise SystemExit(f"READY_SOURCE_CACHE_HASH_MISMATCH:{relative}")
    if not relative.endswith(".vo"):
        continue
    target = destination / Path(relative).relative_to("source")
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)
    if sha(target) != expected:
        raise SystemExit(f"MATERIALIZED_SOURCE_HASH_MISMATCH:{relative}")
    copied[str(target.relative_to(destination))] = expected
required = {
    "util/all.vo", "util/notation.vo", "behavior/time.vo", "behavior/job.vo",
    "behavior/arrival_sequence.vo", "behavior/schedule.vo",
    "behavior/service.vo", "behavior/ready.vo",
}
if set(copied) != required:
    raise SystemExit(f"SOURCE_REUSE_SET_MISMATCH:{sorted(set(copied) ^ required)}")
evidence = {
    "status": "PASS",
    "mode": "VERIFIED_CACHE",
    "producer_snapshot": manifest["snapshot_id"],
    "producer_prepare_manifest_sha256": sha(manifest_path),
    "semantic_acceptance_inferred": False,
    "materialized_files": copied,
}
evidence_path.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
PY
(
  cd "$work/source"
  opam exec --switch="$ROCQ_SWITCH" -- rocq c \
    -R "$work/source" prosa behavior/all.v \
    > "$log_dir/rocq_source_all.log" 2>&1
)
stage_end=$(now_ns)
record_stage source_acquisition "$stage_start" "$stage_end" PASS \
  FRESH_WITH_VERIFIED_DEPENDENCY_REUSE 1 1

# Verify every cached Lean dependency byte, then compile only the new
# aggregator and its aggregator-only interface fixture.
stage_start=$(now_ns)
python3 - "$ready_cache/olean" "$ready_build_manifest" "$work/olean" \
  "$work/lean_dependency_reuse.json" <<'PY'
import hashlib, json, shutil, sys
from pathlib import Path

olean_root, manifest_path, destination, evidence_path = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads(manifest_path.read_text())
if manifest.get("status") != "PASS" or manifest.get("module_count") != 30:
    raise SystemExit("READY_LEAN_BUILD_MANIFEST_INVALID")
verified = {}
for relative, item in manifest["modules"].items():
    path = olean_root / relative
    if not path.is_file() or path.stat().st_size != item["bytes"] or sha(path) != item["sha256"]:
        raise SystemExit(f"READY_LEAN_CACHE_HASH_MISMATCH:{relative}")
    target = destination / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(path, target)
    if sha(target) != item["sha256"]:
        raise SystemExit(f"MATERIALIZED_LEAN_HASH_MISMATCH:{relative}")
    verified[relative] = item["sha256"]
required = {
    "Prosa/Behavior/Time.olean", "Prosa/Behavior/Job.olean",
    "Prosa/Behavior/Arrival_sequence.olean", "Prosa/Behavior/Schedule.olean",
    "Prosa/Behavior/Service.olean", "Prosa/Behavior/Ready.olean",
}
if not required <= set(verified):
    raise SystemExit("READY_LEAN_CACHE_MISSING_BEHAVIOR_DEPENDENCY")
evidence = {
    "status": "PASS",
    "mode": "VERIFIED_CACHE",
    "producer_build_manifest_sha256": sha(manifest_path),
    "verified_module_count": len(verified),
    "materialized_destination": str(destination),
    "semantic_acceptance_inferred": False,
    "verified_modules": verified,
}
evidence_path.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
PY
if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Behavior/All.lean"; then
  echo "forbidden production proof escape" >&2
  exit 1
fi
mathlib_path=$(cd "$PROJECT_ROOT" && lake env printenv LEAN_PATH)
export LEAN_PATH="$work/olean:$PROJECT_ROOT:$mathlib_path"
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Prosa/Behavior/All.olean" \
  "$PROJECT_ROOT/Prosa/Behavior/All.lean" \
  > "$log_dir/lean_behavior_all.log" 2>&1
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/translation_order/BehaviorAllInterface.olean" \
  "$fixture" > "$work/interface.log" 2>&1
cp "$work/interface.log" "$log_dir/interface.log"
stage_end=$(now_ns)
record_stage lean_build "$stage_start" "$stage_end" PASS \
  FRESH_WITH_VERIFIED_DEPENDENCY_REUSE 1 1

# Check the exact source/import mapping and all six current acceptance/hash
# bindings rather than treating cached artifacts as semantic evidence.
stage_start=$(now_ns)
python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$pipeline_dir" "$ready_cache" \
  "$work" <<'PY'
import hashlib, json, re, sys
from pathlib import Path

project, source, pipeline, cache, work = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

source_text = (source / "behavior/all.v").read_text()
lean_text = (project / "Prosa/Behavior/All.lean").read_text()
source_deps = re.findall(
    r"^Require Export prosa\.behavior\.([A-Za-z0-9_]+)\.$",
    source_text, re.MULTILINE,
)
lean_deps = re.findall(
    r"^import Prosa\.Behavior\.([A-Za-z0-9_]+)$", lean_text, re.MULTILINE,
)
mapping = {
    "time": "Time", "job": "Job", "arrival_sequence": "Arrival_sequence",
    "schedule": "Schedule", "service": "Service", "ready": "Ready",
}
expected_source = list(mapping)
expected_lean = list(mapping.values())
interface_errors = []
if source_deps != expected_source:
    interface_errors.append("authoritative Require Export list/order changed")
if lean_deps != expected_lean:
    interface_errors.append("Lean import list/order differs from authoritative mapping")
(work / "source_import_interface_audit.json").write_text(json.dumps({
    "status": "PASS" if not interface_errors else "FAIL_SOURCE_INTERFACE_AUDIT",
    "source_require_exports": source_deps,
    "lean_imports": lean_deps,
    "mapped_expected_lean_imports": expected_lean,
    "errors": interface_errors,
}, indent=2) + "\n")
if interface_errors:
    raise SystemExit(interface_errors)

records = [
    ("behavior/time.v", "Time", "foundation_slice_1_status.json",
     "foundation_slice_1_manifest.json", "artifacts.fresh_olean_sha256",
     "artifacts.lean_source_sha256"),
    ("behavior/job.v", "Job", "behavior_job_module_status.json",
     "behavior_job_module_manifest.json", "production_olean_sha256",
     "production_source_sha256"),
    ("behavior/arrival_sequence.v", "Arrival_sequence",
     "behavior_arrival_sequence_module_status.json",
     "behavior_arrival_sequence_module_manifest.json", "production_olean_sha256",
     "production_source_sha256"),
    ("behavior/schedule.v", "Schedule", "behavior_schedule_module_status.json",
     "behavior_schedule_module_manifest.json", "production_olean_sha256",
     "production_source_sha256"),
    ("behavior/service.v", "Service", "behavior_service_module_status.json",
     "behavior_service_module_manifest.json", "production_olean_sha256",
     "production_source_sha256"),
    ("behavior/ready.v", "Ready", "behavior_ready_module_status.json",
     "behavior_ready_module_manifest.json", "production_olean_sha256",
     "production_source_sha256"),
]
def nested(data, key):
    for part in key.split("."):
        data = data[part]
    return data

entries, errors = [], []
for src, stem, status_name, manifest_name, olean_key, source_key in records:
    status_path = pipeline / status_name
    manifest_path = pipeline / manifest_name
    status = json.loads(status_path.read_text())
    manifest = json.loads(manifest_path.read_text())
    if src == "behavior/time.v":
        file_status = "ACCEPTED_V06_FILE" if (
            status["coverage"]["accepted_files"] >= 1 and
            all(d["acceptance"] == "ACCEPTED_V06_TRANSLATION"
                for d in manifest["declarations"])
        ) else "INVALID"
    else:
        file_status = status["per_file"][src]["status"]
        if manifest.get("acceptance") != "ACCEPTED_V06_FILE":
            errors.append(f"{src}: manifest acceptance missing")
    lean_path = project / "Prosa/Behavior" / f"{stem}.lean"
    olean_path = cache / "olean/Prosa/Behavior" / f"{stem}.olean"
    source_match = sha(lean_path) == nested(manifest, source_key)
    olean_match = sha(olean_path) == nested(manifest, olean_key)
    if file_status != "ACCEPTED_V06_FILE":
        errors.append(f"{src}: dependency status {file_status}")
    if not source_match:
        errors.append(f"{src}: production source hash mismatch")
    if not olean_match:
        errors.append(f"{src}: accepted olean hash mismatch")
    entries.append({
        "source_file": src,
        "status": file_status,
        "production_source_sha256": sha(lean_path),
        "production_source_hash_match": source_match,
        "reused_olean_sha256": sha(olean_path),
        "accepted_olean_hash_match": olean_match,
        "status_evidence": str(status_path.relative_to(project)),
        "status_evidence_sha256": sha(status_path),
        "manifest_evidence": str(manifest_path.relative_to(project)),
        "manifest_evidence_sha256": sha(manifest_path),
    })
result = {
    "status": "PASS" if not errors else "FAIL_DEPENDENCY_CLOSURE",
    "direct_dependency_count": len(entries),
    "all_dependencies_accepted_and_hash_bound": not errors,
    "dependencies": entries,
    "errors": errors,
}
(work / "dependency_closure_audit.json").write_text(
    json.dumps(result, indent=2) + "\n"
)
if errors:
    raise SystemExit(errors)
PY
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$axiom_config" --log "$work/interface.log" \
  --output "$work/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"
jq -e '
  (.missing | length) == 0 and (.extra | length) == 0 and
  (.declarations["Prosa.Validation.BehaviorAllInterface.zeroInstant_eq_zero"].status == "PASS") and
  (.declarations["Prosa.Validation.BehaviorAllInterface.zeroInstant_eq_zero"].unexpected_axioms | length) == 0' \
  "$work/lean_axiom_summary.json" >/dev/null
python3 - "$work/interface.log" <<'PY'
from pathlib import Path
import sys
text = Path(sys.argv[1]).read_text()
expected = [
    "Prosa.Behavior.Time.instant", "Prosa.Behavior.Job.JobType",
    "Prosa.Behavior.Arrival_sequence.arrival_sequence",
    "Prosa.Behavior.Schedule.ProcessorState",
    "Prosa.Behavior.Service.scheduled_at", "Prosa.Behavior.Ready.JobReady",
    "'Prosa.Validation.BehaviorAllInterface.zeroInstant_eq_zero' does not depend on any axioms",
]
missing = [item for item in expected if item not in text]
if missing:
    raise SystemExit("missing compiled behavior interface probes: " + ", ".join(missing))
PY
(cd "$REPO_ROOT" && git diff --check)
stage_end=$(now_ns)
record_stage audit "$stage_start" "$stage_end" PASS FRESH 1 0

for name in export rocq_import certificate_compile; do
  point=$(now_ns)
  record_stage "$name" "$point" "$point" \
    NOT_APPLICABLE_NO_NAMED_SOURCE_DECLARATIONS NOT_APPLICABLE 0 0
done

stage_start=$(now_ns)
cp "$work/olean/Prosa/Behavior/All.olean" "$publish_dir/All.olean"
cp "$work/olean/Validation/fixtures/translation_order/BehaviorAllInterface.olean" \
  "$publish_dir/BehaviorAllInterface.olean"
cp "$work/source/behavior/all.vo" "$publish_dir/source_all.vo"
cp "$work/source_import_interface_audit.json" "$publish_dir/"
cp "$work/dependency_closure_audit.json" "$publish_dir/"
cp "$work/source_dependency_reuse.json" "$publish_dir/"
cp "$work/lean_dependency_reuse.json" "$publish_dir/"
cp "$work/lean_axiom_summary.json" "$publish_dir/"

python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$work" "$log_dir" \
  "$ready_status" "$ready_manifest" \
  "$pipeline_dir/behavior_all_module_manifest.json" \
  "$pipeline_dir/behavior_all_module_status.json" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

project, source, work, logs, previous_status_path, previous_manifest_path, manifest_out, status_out = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
previous = json.loads(previous_status_path.read_text())
previous_manifest = json.loads(previous_manifest_path.read_text())
dependency = json.loads((work / "dependency_closure_audit.json").read_text())
interface = json.loads((work / "source_import_interface_audit.json").read_text())
axioms = json.loads((work / "lean_axiom_summary.json").read_text())
assert previous["coverage"]["accepted_files"] == 26
assert previous["coverage"]["accepted_declarations"] == 247
assert previous_manifest["acceptance"] == "ACCEPTED_V06_FILE"
assert dependency["status"] == "PASS" and interface["status"] == "PASS"
manifest = {
    "slice": "TRANSLATION_ORDER_BEHAVIOR_ALL",
    "generated_at": datetime.now().astimezone().isoformat(),
    "source_file": "behavior/all.v",
    "source_commit": subprocess.check_output(
        ["git", "-C", str(source), "rev-parse", "HEAD"], text=True
    ).strip(),
    "source_file_sha256": sha(source / "behavior/all.v"),
    "public_declaration_count": 0,
    "production_file": "Prosa/Behavior/All.lean",
    "production_source_sha256": sha(project / "Prosa/Behavior/All.lean"),
    "production_olean_sha256": sha(work / "olean/Prosa/Behavior/All.olean"),
    "interface_fixture_source_sha256": sha(
        project / "Validation/fixtures/translation_order/BehaviorAllInterface.lean"
    ),
    "interface_fixture_olean_sha256": sha(
        work / "olean/Validation/fixtures/translation_order/BehaviorAllInterface.olean"
    ),
    "official_source_vo_sha256": sha(work / "source/behavior/all.vo"),
    "source_import_interface_audit_sha256": sha(work / "source_import_interface_audit.json"),
    "dependency_closure_audit_sha256": sha(work / "dependency_closure_audit.json"),
    "source_dependency_reuse_sha256": sha(work / "source_dependency_reuse.json"),
    "lean_dependency_reuse_sha256": sha(work / "lean_dependency_reuse.json"),
    "lean_axiom_audit": axioms,
    "cross_itp_declaration_validation": {
        "applicability": "NOT_APPLICABLE_NO_NAMED_SOURCE_DECLARATIONS",
        "lean4export_executions": 0,
        "rocq_import_executions": 0,
        "semantic_certificates": 0,
        "reason": (
            "The authoritative module declares no named object. Its observable "
            "aggregation boundary is validated compositionally from six accepted "
            "dependencies, the byte-identical compiled Rocq module, and an actual "
            "compiled Lean aggregator-only interface probe."
        ),
    },
    "dependency_closure": dependency,
    "interface_audit": interface,
    "accepted_dependency_snapshot": previous_manifest["snapshot_id"],
    "fresh_work_directory": str(work),
    "acceptance": "ACCEPTED_V06_FILE",
}
manifest_out.write_text(json.dumps(manifest, indent=2) + "\n")
status = {
    "slice": "TRANSLATION_ORDER_BEHAVIOR_ALL",
    "per_file": {
        "behavior/all.v": {
            "public_declarations": 0,
            "translated": 0,
            "proof_clean": 0,
            "certified": 0,
            "module_interface_audited": True,
            "direct_dependencies_accepted": 6,
            "status": "ACCEPTED_V06_FILE",
            "reason": (
                "zero-declaration aggregation module; exact re-export mapping, "
                "accepted dependency/hash closure, official Rocq compile, and actual "
                "compiled Lean interface all passed"
            ),
        }
    },
    "coverage": {
        "accepted_files": 27,
        "authoritative_files": 357,
        "accepted_declarations": 247,
        "authoritative_declarations": 2439,
        "translated_but_not_certified": 0,
        "deferred_external_boundary": 239,
    },
    "previous_status_sha256": sha(previous_status_path),
    "status": "PASS",
}
status_out.write_text(json.dumps(status, indent=2) + "\n")
PY
stage_end=$(now_ns)
record_stage publication "$stage_start" "$stage_end" PASS FRESH 1 0

python3 - "$timing_jsonl" "$log_dir/stage_timings.json" \
  "$pipeline_dir/behavior_all_module_manifest.json" <<'PY'
import hashlib, json, sys
from pathlib import Path
source, output, manifest_path = map(Path, sys.argv[1:])
records = [json.loads(line) for line in source.read_text().splitlines() if line]
order = [
    "source_acquisition", "lean_build", "export", "rocq_import",
    "certificate_compile", "audit", "publication",
]
records.sort(key=lambda row: order.index(row["stage"]))
result = {
    "stages": records,
    "total_elapsed_seconds": sum(row["elapsed_seconds"] for row in records),
    "execution_count": sum(row["execution_count"] for row in records),
    "cache_hits": sum(row["cache_hits"] for row in records),
}
output.write_text(json.dumps(result, indent=2) + "\n")
manifest = json.loads(manifest_path.read_text())
manifest["timing_evidence"] = str(output)
manifest["timing_evidence_sha256"] = hashlib.sha256(output.read_bytes()).hexdigest()
manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
PY

(cd "$REPO_ROOT" && git diff --check)
echo "behavior/all.v aggregation interface: ACCEPTED_V06_FILE"
echo "fresh work directory: $work"
echo "timing evidence: $log_dir/stage_timings.json"
