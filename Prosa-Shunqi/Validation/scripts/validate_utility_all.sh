#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

log_root="$VALIDATION_ROOT/logs/translation_order/all"
run_stamp=$(date '+%Y%m%d_%H%M%S_%z')
log_dir="$log_root/finalize_$run_stamp"
publish_dir="$VALIDATION_ROOT/imported/translation_order/all"
pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
fixture="$VALIDATION_ROOT/fixtures/translation_order/UtilAllInterface.lean"
axiom_config="$VALIDATION_ROOT/fixtures/translation_order/util_all_lean_axiom_config.json"
mkdir -p "$log_dir" "$publish_dir"

work=$(validation_fresh_workdir utility_all_finalize)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/translation_order" "$work/source"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"

timing_jsonl="$log_dir/stage_timings.jsonl"
: > "$timing_jsonl"
now_ns() { python3 -c 'import time; print(time.time_ns())'; }
record_stage() {
  local stage=$1 start=$2 end=$3 status=$4 execution_count=$5 cache_hits=$6
  python3 - "$timing_jsonl" "$stage" "$start" "$end" "$status" \
    "$execution_count" "$cache_hits" <<'PY'
import json, sys
path, stage, start, end, status, executions, hits = sys.argv[1:]
record = {
    "stage": stage,
    "status": status,
    "provenance": "FRESH",
    "execution_count": int(executions),
    "cache_hits": int(hits),
    "elapsed_seconds": (int(end) - int(start)) / 1_000_000_000,
}
with open(path, "a") as f:
    f.write(json.dumps(record, sort_keys=True) + "\n")
PY
}

stage_start=$(now_ns)
[[ $(validation_sha256 "$SOURCE_ROOT/util/all.v") == \
  d176f8e4883818919450aaf0ecb0a65544274ede913b04b28ad1f29957293025 ]]
[[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/all.v" for r in csv.DictReader(open(sys.argv[1]))))' \
  "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 0 ]]
cp "$SOURCE_ROOT/util/all.v" "$work/source/all.v"
python3 - "$work/source/all.v" "$PROJECT_ROOT/Prosa/Util/All.lean" \
  "$work/source/import_interface_audit.json" <<'PY'
import json, re, sys
from pathlib import Path

source, lean, output = map(Path, sys.argv[1:])
source_text = source.read_text()
lean_text = lean.read_text()
source_internal = re.findall(
    r"^Require Export prosa\.util\.([A-Za-z0-9_]+)\.$",
    source_text, re.MULTILINE,
)
source_external = []
for line in source_text.splitlines():
    if line.startswith("From mathcomp Require Export "):
        names = line.removeprefix("From mathcomp Require Export ").removesuffix(".").split()
        source_external.extend(f"mathcomp.{name}" for name in names)
    elif line == "Require Export mathcomp.zify.zify.":
        source_external.append("mathcomp.zify.zify")

name_map = {
    "notation": "Notation", "bigcat": "Bigcat", "bigop": "Bigop",
    "div_mod": "Div_mod", "list": "List", "nat": "Nat", "sum": "Sum",
    "seqset": "Seqset", "unit_growth": "UnitGrowth", "epsilon": "Epsilon",
    "search_arg": "SearchArg", "rel": "Rel", "minmax": "Minmax",
    "supremum": "Supremum", "nondecreasing": "Nondecreasing",
    "setoid": "Setoid", "tactics": "Tactics", "poet": "Poet",
}
expected_internal = [name_map[name] for name in source_internal]
lean_internal = re.findall(
    r"^import Prosa\.Util\.([A-Za-z0-9_]+)$", lean_text, re.MULTILINE
)
expected_external = [
    "mathcomp.ssreflect", "mathcomp.ssrnat", "mathcomp.ssrbool",
    "mathcomp.eqtype", "mathcomp.fintype", "mathcomp.bigop",
    "mathcomp.zify.zify",
]
errors = []
if source_internal != list(name_map):
    errors.append("authoritative internal Require Export list changed")
if lean_internal != expected_internal:
    errors.append("Lean aggregation import list/order differs from authoritative mapping")
if source_external != expected_external:
    errors.append("authoritative external Require Export list changed")
result = {
    "status": "PASS" if not errors else "FAIL_SOURCE_INTERFACE_AUDIT",
    "source_internal_require_exports": source_internal,
    "lean_internal_imports": lean_internal,
    "mapped_expected_lean_imports": expected_internal,
    "source_external_require_exports": source_external,
    "external_boundary_mapping": (
        "The pinned Mathlib interfaces imported transitively by the 18 accepted "
        "Lean utility modules replace the source MathComp aggregation boundary."
    ),
    "errors": errors,
}
output.write_text(json.dumps(result, indent=2) + "\n")
if errors:
    raise SystemExit(1)
PY
stage_end=$(now_ns)
record_stage source_acquisition "$stage_start" "$stage_end" PASS 1 0

stage_start=$(now_ns)
if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/All.lean"; then
  echo "forbidden production proof escape" >&2
  exit 1
fi
modules=(
  Tactics Notation Rel Seqset Subadditivity Supremum Nat UnitGrowth
  SearchArg List Sum Epsilon Bigop Setoid Poet Bigcat Minmax Div_mod
  Nondecreasing All
)
for module in "${modules[@]}"; do
  validation_compile_lean_module "$work" "Prosa/Util/$module" \
    > "$log_dir/fresh_${module}.log" 2>&1
done
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/translation_order/UtilAllInterface.olean" \
  "$fixture" > "$work/interface.log" 2>&1
cp "$work/interface.log" "$log_dir/interface.log"
stage_end=$(now_ns)
record_stage lean_build "$stage_start" "$stage_end" PASS 1 0

stage_start=$(now_ns)
python3 - "$PROJECT_ROOT" "$pipeline_dir" \
  "$work/dependency_closure_audit.json" <<'PY'
import hashlib, json, sys
from pathlib import Path

project, pipeline, output = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
stem = {
    "util/notation.v": "Notation", "util/bigcat.v": "Bigcat",
    "util/bigop.v": "Bigop", "util/div_mod.v": "Div_mod",
    "util/list.v": "List", "util/nat.v": "Nat", "util/sum.v": "Sum",
    "util/seqset.v": "Seqset", "util/unit_growth.v": "UnitGrowth",
    "util/epsilon.v": "Epsilon", "util/search_arg.v": "SearchArg",
    "util/rel.v": "Rel", "util/minmax.v": "Minmax",
    "util/supremum.v": "Supremum",
    "util/nondecreasing.v": "Nondecreasing", "util/setoid.v": "Setoid",
    "util/tactics.v": "Tactics", "util/poet.v": "Poet",
}
foundation = {
    "util/notation.v", "util/tactics.v", "util/rel.v", "util/seqset.v",
    "util/supremum.v",
}
expansion = {
    "util/nat.v", "util/unit_growth.v", "util/search_arg.v",
    "util/list.v", "util/sum.v",
}
module_file = {
    "util/epsilon.v": "epsilon", "util/bigop.v": "bigop",
    "util/setoid.v": "setoid", "util/poet.v": "poet",
    "util/bigcat.v": "bigcat", "util/minmax.v": "minmax",
    "util/div_mod.v": "div_mod", "util/nondecreasing.v": "nondecreasing",
}
closure_status = json.loads((pipeline / "foundation_slice_2_closure_status.json").read_text())
closure_manifest_path = pipeline / "foundation_slice_2_closure_manifest.json"
closure_manifest = json.loads(closure_manifest_path.read_text())
expansion_status_path = pipeline / "utility_foundation_expansion_status.json"
expansion_status = json.loads(expansion_status_path.read_text())
expansion_manifest_path = pipeline / "utility_foundation_expansion_manifest.json"
expansion_manifest = json.loads(expansion_manifest_path.read_text())
entries, errors = [], []
for src, lean_stem in stem.items():
    lean_path = project / "Prosa/Util" / f"{lean_stem}.lean"
    current_hash = sha(lean_path)
    if src in foundation:
        status_path = pipeline / "foundation_slice_2_closure_status.json"
        status = closure_status["per_file"][src]["status"]
        evidence_path = closure_manifest_path
        bound_hashes = [closure_manifest["files"][src]["lean_source_sha256"]]
    elif src in expansion:
        status_path = expansion_status_path
        status = expansion_status["per_file"][src]["status"]
        evidence_path = expansion_manifest_path
        bound_hashes = sorted({
            c["lean_source_sha256"] for c in expansion_manifest["clusters"]
            if c.get("source_file") == src
        })
    else:
        key = module_file[src]
        status_path = pipeline / f"{key}_module_status.json"
        evidence_path = pipeline / f"{key}_module_manifest.json"
        status_data = json.loads(status_path.read_text())
        evidence = json.loads(evidence_path.read_text())
        status = status_data["per_file"][src]["status"]
        bound_hashes = [evidence["production_source_sha256"]]
        if evidence.get("acceptance") != "ACCEPTED_V06_FILE":
            errors.append(f"{src}: manifest acceptance is not ACCEPTED_V06_FILE")
    hash_match = current_hash in bound_hashes
    if status != "ACCEPTED_V06_FILE":
        errors.append(f"{src}: dependency status is {status}")
    if not hash_match:
        errors.append(f"{src}: production source hash is not bound by acceptance evidence")
    entries.append({
        "source_file": src,
        "production_file": str(lean_path.relative_to(project)),
        "acceptance_status": status,
        "production_source_sha256": current_hash,
        "accepted_bound_hashes": bound_hashes,
        "hash_match": hash_match,
        "status_evidence": str(status_path.relative_to(project)),
        "status_evidence_sha256": sha(status_path),
        "manifest_evidence": str(evidence_path.relative_to(project)),
        "manifest_evidence_sha256": sha(evidence_path),
    })
result = {
    "status": "PASS" if not errors else "FAIL_DEPENDENCY_CLOSURE",
    "direct_dependency_count": len(entries),
    "all_dependencies_accepted": not errors,
    "dependencies": entries,
    "errors": errors,
}
output.write_text(json.dumps(result, indent=2) + "\n")
if errors:
    raise SystemExit(1)
PY
stage_end=$(now_ns)
record_stage dependency_closure_audit "$stage_start" "$stage_end" PASS 1 0

stage_start=$(now_ns)
python3 "$script_dir/audit_lean_axioms.py" \
  --config "$axiom_config" --log "$work/interface.log" \
  --output "$work/lean_axiom_summary.json" \
  > "$log_dir/lean_axiom_classifier.log"
jq -e '
  (.missing | length) == 0 and (.extra | length) == 0 and
  (.declarations["Prosa.Validation.UtilAllInterface.epsilonValue_eq_one"].status == "PASS") and
  (.declarations["Prosa.Validation.UtilAllInterface.epsilonValue_eq_one"].unexpected_axioms | length) == 0' \
  "$work/lean_axiom_summary.json" >/dev/null
python3 - "$work/interface.log" <<'PY'
from pathlib import Path
import sys
text = Path(sys.argv[1]).read_text()
expected = [
    "Prosa.Util.Notation.constant", "Prosa.Util.Bigcat.bigCatFin",
    "Prosa.Util.Bigop.bigSeq", "Prosa.Util.Div_mod.eqdivn_leqmodn",
    "Prosa.Util.List.max0", "Prosa.Util.Nat.subnACA",
    "Prosa.Util.Sum.sumSeq", "Prosa.Util.Seqset.set",
    "Prosa.Util.UnitGrowth.unit_growth_function",
    "Prosa.Util.SearchArg.search_arg", "Prosa.Util.Rel.monotone",
    "Prosa.Util.Minmax.bigMaxListCond", "Prosa.Util.Supremum.supremum",
    "Prosa.Util.Nondecreasing.distances", "Prosa.Util.Setoid.leb",
    "Prosa.Util.Tactics.neqP",
    "Prosa.Util.Poet.forall_exists_implied_by_forall_in_zip",
    "'Prosa.Validation.UtilAllInterface.epsilonValue_eq_one' does not depend on any axioms",
]
missing = [item for item in expected if item not in text]
if missing:
    raise SystemExit("missing compiled interface probes: " + ", ".join(missing))
PY
(cd "$REPO_ROOT" && git diff --check)
stage_end=$(now_ns)
record_stage audit "$stage_start" "$stage_end" PASS 1 0

stage_start=$(now_ns)
cp "$work/olean/Prosa/Util/All.olean" "$publish_dir/All.olean"
cp "$work/olean/Validation/fixtures/translation_order/UtilAllInterface.olean" \
  "$publish_dir/UtilAllInterface.olean"
cp "$work/source/import_interface_audit.json" \
  "$publish_dir/import_interface_audit.json"
cp "$work/dependency_closure_audit.json" \
  "$publish_dir/dependency_closure_audit.json"
cp "$work/lean_axiom_summary.json" "$publish_dir/lean_axiom_summary.json"

python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$work" "$log_dir" \
  "$pipeline_dir/nondecreasing_module_status.json" \
  "$pipeline_dir/util_all_module_manifest.json" \
  "$pipeline_dir/util_all_module_status.json" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

project, source, work, logs, previous_path, manifest_out, status_out = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
previous = json.loads(previous_path.read_text())
dependency_audit = json.loads((work / "dependency_closure_audit.json").read_text())
interface_audit = json.loads((work / "source/import_interface_audit.json").read_text())
axiom_audit = json.loads((work / "lean_axiom_summary.json").read_text())
assert previous["coverage"]["accepted_files"] == 20
assert previous["coverage"]["accepted_declarations"] == 204
assert dependency_audit["status"] == "PASS"
assert interface_audit["status"] == "PASS"
manifest = {
    "slice": "TRANSLATION_ORDER_UTIL_ALL",
    "generated_at": datetime.now().astimezone().isoformat(),
    "source_file": "util/all.v",
    "source_commit": subprocess.check_output(
        ["git", "-C", str(source), "rev-parse", "HEAD"], text=True
    ).strip(),
    "source_file_sha256": sha(source / "util/all.v"),
    "public_declaration_count": 0,
    "production_file": "Prosa/Util/All.lean",
    "production_source_sha256": sha(project / "Prosa/Util/All.lean"),
    "production_olean_sha256": sha(work / "olean/Prosa/Util/All.olean"),
    "interface_fixture_source_sha256": sha(
        project / "Validation/fixtures/translation_order/UtilAllInterface.lean"
    ),
    "interface_fixture_olean_sha256": sha(
        work / "olean/Validation/fixtures/translation_order/UtilAllInterface.olean"
    ),
    "source_import_interface_audit_sha256": sha(
        work / "source/import_interface_audit.json"
    ),
    "dependency_closure_audit_sha256": sha(
        work / "dependency_closure_audit.json"
    ),
    "lean_axiom_audit": axiom_audit,
    "cross_itp_declaration_validation": {
        "applicability": "NOT_APPLICABLE_NO_NAMED_SOURCE_DECLARATIONS",
        "lean4export_executions": 0,
        "rocq_import_executions": 0,
        "semantic_certificates": 0,
        "reason": (
            "The authoritative module declares no object to export. Its observable "
            "aggregation boundary is validated compositionally from 18 accepted "
            "module dependencies plus an actual compiled Lean interface probe."
        ),
    },
    "dependency_closure": dependency_audit,
    "interface_audit": interface_audit,
    "fresh_work_directory": str(work),
    "acceptance": "ACCEPTED_V06_FILE",
}
manifest_out.write_text(json.dumps(manifest, indent=2) + "\n")
status = {
    "slice": "TRANSLATION_ORDER_UTIL_ALL",
    "per_file": {
        "util/all.v": {
            "public_declarations": 0,
            "translated": 0,
            "proof_clean": 0,
            "certified": 0,
            "module_interface_audited": True,
            "direct_dependencies_accepted": 18,
            "status": "ACCEPTED_V06_FILE",
            "reason": (
                "zero-declaration aggregation module; exact import/re-export mapping, "
                "dependency acceptance closure, actual compiled interface, and notation "
                "visibility all passed"
            ),
        }
    },
    "coverage": {
        "accepted_files": 21,
        "authoritative_files": 357,
        "accepted_declarations": 204,
        "authoritative_declarations": 2439,
        "translated_but_not_certified": 0,
        "deferred_external_boundary": 239,
    },
    "previous_status_sha256": sha(previous_path),
    "status": "PASS",
}
status_out.write_text(json.dumps(status, indent=2) + "\n")
PY
stage_end=$(now_ns)
record_stage publication "$stage_start" "$stage_end" PASS 1 0

python3 - "$timing_jsonl" "$log_dir/stage_timings.json" \
  "$pipeline_dir/util_all_module_manifest.json" <<'PY'
import hashlib, json, sys
from pathlib import Path
source, output, manifest_path = map(Path, sys.argv[1:])
records = [json.loads(line) for line in source.read_text().splitlines() if line]
for name in ("export", "rocq_import", "certificate_compile"):
    records.append({
        "stage": name,
        "status": "NOT_APPLICABLE_NO_NAMED_SOURCE_DECLARATIONS",
        "provenance": "NOT_APPLICABLE",
        "execution_count": 0,
        "cache_hits": 0,
        "elapsed_seconds": 0.0,
    })
records.sort(key=lambda r: [
    "source_acquisition", "lean_build", "export", "rocq_import",
    "certificate_compile", "dependency_closure_audit", "audit", "publication",
].index(r["stage"]))
result = {
    "stages": records,
    "total_elapsed_seconds": sum(r["elapsed_seconds"] for r in records),
    "execution_count": sum(r["execution_count"] for r in records),
    "cache_hits": sum(r["cache_hits"] for r in records),
}
output.write_text(json.dumps(result, indent=2) + "\n")
manifest = json.loads(manifest_path.read_text())
manifest["timing_evidence"] = str(output)
manifest["timing_evidence_sha256"] = hashlib.sha256(output.read_bytes()).hexdigest()
manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
PY

(cd "$REPO_ROOT" && git diff --check)
echo "util/all.v aggregation interface: ACCEPTED_V06_FILE"
echo "fresh work directory: $work"
echo "timing evidence: $log_dir/stage_timings.json"
