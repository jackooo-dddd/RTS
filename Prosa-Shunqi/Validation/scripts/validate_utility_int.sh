#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "$0")" && pwd)
source "$script_dir/common/validation_common.sh"
validation_common_init "$script_dir"
validation_verify_tool_hashes

pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
previous_status="$pipeline_dir/model_processor_supply_module_status.json"
selection="$pipeline_dir/util_int_selection.json"
fixture="$VALIDATION_ROOT/fixtures/translation_order/IntModuleInterface.lean"
publish_dir="$VALIDATION_ROOT/imported/translation_order/int"
report="$PROJECT_ROOT/Reports/files/util/2026-09-23_072030_int.md"
run_report="$PROJECT_ROOT/Reports/runs/2026-09-22_000308_translation_order_continuous_run.md"
run_stamp=$(date '+%Y%m%d_%H%M%S_%z')
log_dir="$VALIDATION_ROOT/logs/translation_order/util_int/finalize_$run_stamp"
mkdir -p "$publish_dir" "$log_dir"

jq -e '.status == "PASS" and
  .coverage.accepted_files == 28 and
  .coverage.accepted_declarations == 252 and
  .coverage.translated_but_not_certified == 0 and
  .per_file["model/processor/supply.v"].status == "ACCEPTED_V06_FILE"' \
  "$previous_status" >/dev/null
jq -e '.FILE_DAG_READY == true and .execution_rank == 29 and
  .source_file == "util/int.v" and .public_declaration_count == 0' \
  "$selection" >/dev/null
[[ $(validation_sha256 "$SOURCE_ROOT/util/int.v") == \
  3edf932c0b7a4d68d21e5c153cfa2d6d402d3d21210160507ddc141c40130da8 ]]
[[ $(git -C "$SOURCE_ROOT" rev-parse HEAD) == \
  414e66760333eaa4ef78c685bcf53291c527a548 ]]
[[ -z $(git -C "$SOURCE_ROOT" status --porcelain) ]]
[[ $(python3 -c 'import csv,sys; print(sum(r["source_file"]=="util/int.v" for r in csv.DictReader(open(sys.argv[1]))))' \
  "$VALIDATION_ROOT/planning/v06_dependency/declaration_inventory.csv") == 0 ]]
if rg -n '\b(sorry|axiom|unsafe)\b' "$PROJECT_ROOT/Prosa/Util/Int.lean"; then
  echo "forbidden production proof escape" >&2
  exit 1
fi

work=$(validation_fresh_workdir utility_int_finalize)
mkdir -p "$work/olean/Prosa/Util" \
  "$work/olean/Validation/fixtures/translation_order" \
  "$work/source/util"
validation_prepare_lean_path "$work"
printf '%s\n' "$work" > "$log_dir/fresh_workdir.txt"
timings="$log_dir/stage_timings.jsonl"
: > "$timings"

now_ns() { python3 -c 'import time; print(time.time_ns())'; }
record_stage() {
  local stage=$1 start=$2 end=$3 status=$4 mode=$5 executed=$6
  python3 - "$timings" "$stage" "$start" "$end" "$status" "$mode" "$executed" <<'PY'
import json, sys
path, stage, start, end, status, mode, executed = sys.argv[1:]
with open(path, "a") as stream:
    stream.write(json.dumps({
        "stage": stage,
        "status": status,
        "mode": mode,
        "executed": executed == "true",
        "execution_count": 1 if executed == "true" else 0,
        "cache_hits": 0,
        "elapsed_seconds": (int(end) - int(start)) / 1_000_000_000,
    }, sort_keys=True) + "\n")
PY
}

stage_start=$(now_ns)
validation_compile_lean_module "$work" Prosa/Util/Int \
  > "$log_dir/fresh_Int.log" 2>&1
lean -DautoImplicit=false -R "$PROJECT_ROOT" \
  -o "$work/olean/Validation/fixtures/translation_order/IntModuleInterface.olean" \
  "$fixture" > "$log_dir/interface_compile_and_axioms.log" 2>&1
stage_end=$(now_ns)
record_stage lean_build "$stage_start" "$stage_end" PASS FRESH true

stage_start=$(now_ns)
cp "$SOURCE_ROOT/util/int.v" "$work/source/util/int.v"
cmp -s "$SOURCE_ROOT/util/int.v" "$work/source/util/int.v"
(cd "$work/source" && opam exec --switch="$ROCQ_SWITCH" -- \
  rocq c -R "$work/source" prosa util/int.v) \
  > "$log_dir/source_compile.log" 2>&1
stage_end=$(now_ns)
record_stage source_acquisition "$stage_start" "$stage_end" PASS FRESH true

for stage in export rocq_import certificate_compile; do
  instant=$(now_ns)
  record_stage "$stage" "$instant" "$instant" NOT_APPLICABLE \
    ZERO_PUBLIC_DECLARATIONS false
done

stage_start=$(now_ns)
python3 - "$SOURCE_ROOT/util/int.v" "$PROJECT_ROOT/Prosa/Util/Int.lean" \
  "$log_dir/interface_compile_and_axioms.log" "$work/interface_audit.json" <<'PY'
import json, re, sys
from pathlib import Path
source_path, lean_path, log_path, output = map(Path, sys.argv[1:])
source = source_path.read_text()
lean = lean_path.read_text()
source_exports = re.findall(
    r"^From mathcomp Require Export ([^.]+)\.$", source, re.MULTILINE)
theory_exports = re.findall(r"^Export ([^.]+(?:\.[A-Za-z]+)?(?: [^.]+(?:\.[A-Za-z]+)?)*)\.$", source, re.MULTILINE)
lean_imports = re.findall(r"^import ([A-Za-z0-9_.]+)$", lean, re.MULTILINE)
log = log_path.read_text()
audited = ["carrier", "ofNat", "negSucc", "add", "sub", "le", "lt"]
errors = []
if source_exports != ["ssralg ssrnum ssrint order"]:
    errors.append(f"source Require Export changed: {source_exports}")
if theory_exports != ["Order.Theory GRing.Theory Num.Theory"]:
    errors.append(f"source theory Export changed: {theory_exports}")
if lean_imports != ["Mathlib.Algebra.Order.Ring.Int"]:
    errors.append(f"Lean import boundary changed: {lean_imports}")
for name in audited:
    expected = f"'Prosa.Validation.IntModuleInterface.{name}' does not depend on any axioms"
    if expected not in log:
        errors.append(f"missing clean axiom result: {name}")
if "depends on axioms:" in log or "sorryAx" in log:
    errors.append("unexpected axiom in interface audit")
result = {
    "status": "PASS" if not errors else "FAIL_INTERFACE_AUDIT",
    "source_require_exports": source_exports,
    "source_theory_exports": theory_exports,
    "lean_imports": lean_imports,
    "observable_interfaces": audited,
    "axiom_status": "KERNEL_PROVED_NO_AXIOMS" if not errors else "FAIL",
    "scope_note": "This audits the zero-declaration re-export boundary; it does not claim that all of MathComp is isomorphic to Mathlib.",
    "errors": errors,
}
output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
if errors:
    raise SystemExit("; ".join(errors))
PY
stage_end=$(now_ns)
record_stage assumption_audit "$stage_start" "$stage_end" PASS FRESH true

stage_start=$(now_ns)
cp "$work/olean/Prosa/Util/Int.olean" "$publish_dir/Int.olean"
cp "$work/olean/Validation/fixtures/translation_order/IntModuleInterface.olean" \
  "$publish_dir/IntModuleInterface.olean"
cp "$work/source/util/int.vo" "$publish_dir/source_int.vo"
cp "$work/interface_audit.json" "$publish_dir/interface_audit.json"

python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$work" "$log_dir" \
  "$previous_status" "$selection" "$pipeline_dir/util_int_module_manifest.json" \
  "$pipeline_dir/util_int_module_status.json" "$report" "$run_report" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

(project, source, work, logs, previous_path, selection_path, manifest_out,
 status_out, report, run_report) = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
previous = json.loads(previous_path.read_text())
selection = json.loads(selection_path.read_text())
interface = json.loads((work / "interface_audit.json").read_text())
stages = [json.loads(line) for line in (logs / "stage_timings.jsonl").read_text().splitlines()]
fingerprint_parts = [
    sha(source / "util/int.v"), sha(project / "Prosa/Util/Int.lean"),
    sha(project / "Validation/fixtures/translation_order/IntModuleInterface.lean"),
    sha(project / "lean-toolchain"), sha(project / "lake-manifest.json"),
]
snapshot = hashlib.sha256("\n".join(fingerprint_parts).encode()).hexdigest()
now = datetime.now().astimezone().isoformat()
manifest = {
    "schema_version": 1,
    "slice": "TRANSLATION_ORDER_UTIL_INT",
    "generated_at": now,
    "snapshot_id": snapshot,
    "source_file": "util/int.v",
    "source_commit": subprocess.check_output(
        ["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip(),
    "source_file_sha256": sha(source / "util/int.v"),
    "source_declaration_count": 0,
    "production_file": "Prosa/Util/Int.lean",
    "production_source_sha256": sha(project / "Prosa/Util/Int.lean"),
    "production_olean_sha256": sha(work / "olean/Prosa/Util/Int.olean"),
    "validation_interface_source_sha256": sha(project / "Validation/fixtures/translation_order/IntModuleInterface.lean"),
    "validation_interface_olean_sha256": sha(work / "olean/Validation/fixtures/translation_order/IntModuleInterface.olean"),
    "official_rocq_vo_sha256": sha(work / "source/util/int.vo"),
    "selection_sha256": sha(selection_path),
    "interface_audit": interface,
    "stages": stages,
    "semantic_scope": {
        "kind": "ZERO_DECLARATION_EXTERNAL_INTERFACE_AUDIT",
        "declaration_certificates": [],
        "reason": "The source introduces no Prosa declaration; the exact re-export boundary and actual compiled target interface are audited without inventing a vacuous declaration certificate.",
        "future_bridge_boundary": "Individual declarations using MathComp int must certify their required Int operations compositionally."
    },
    "acceptance": "ACCEPTED_V06_FILE",
}
manifest_out.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
status = {
    "slice": "TRANSLATION_ORDER_UTIL_INT",
    "per_file": {
        "util/int.v": {
            "public_declarations": 0,
            "translated": 0,
            "proof_clean": 0,
            "certified": 0,
            "module_interface_audited": True,
            "status": "ACCEPTED_V06_FILE",
            "reason": "zero-declaration external MathComp integer/order re-export boundary; exact source exports, official Rocq compile, actual Lean import and observable Int interfaces passed"
        }
    },
    "coverage": {
        "accepted_files": 29,
        "authoritative_files": 357,
        "accepted_declarations": 252,
        "authoritative_declarations": 2439,
        "translated_but_not_certified": 0,
        "deferred_external_boundary": 239,
    },
    "previous_status_sha256": sha(previous_path),
    "snapshot_id": snapshot,
    "status": "PASS",
}
assert previous["coverage"]["accepted_files"] == 28
assert previous["coverage"]["accepted_declarations"] == 252
status_out.write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")

block = f'''<!-- FORMAL_PUBLICATION_BEGIN -->
## {now} — formal module-interface acceptance

The byte-identical official Rocq module and the actual compiled Lean module
interface both passed. The source has zero named public declarations, so no
vacuous declaration-level semantic certificate is claimed. The audit checked
the exact four MathComp `Require Export` modules and three exported theory
namespaces against the deliberate Mathlib `Int` ordered-ring import, then
compiled validation-only observations of the integer carrier, its two
constructor branches, natural embedding, addition, subtraction, order, ring
instances, and decidable equality.

All seven named observable probes are axiom-free. Export, Rocq import, and
certificate stages are explicitly `NOT_APPLICABLE` because there is no Prosa
declaration in this file; downstream declarations that use integers must still
certify each required operation under an explicit MathComp-int/Lean-Int
relation. Snapshot: `{snapshot}`.

Cumulative machine coverage is **29 / 357 files** and **252 / 2439
declarations**, with zero translated-but-not-certified debt.

Final file status: **ACCEPTED_V06_FILE**.
<!-- FORMAL_PUBLICATION_END -->'''
text = report.read_text()
begin, end = "<!-- FORMAL_PUBLICATION_BEGIN -->", "<!-- FORMAL_PUBLICATION_END -->"
if begin in text:
    text = text[:text.index(begin)].rstrip() + "\n\n" + block + "\n"
else:
    text = text.rstrip() + "\n\n" + block + "\n"
report.write_text(text)
with run_report.open("a") as stream:
    stream.write(f'''\n\n## {now} — util/int module boundary accepted\n\n''')
    stream.write("- The source contains zero named declarations; exact source re-exports and the actual compiled Lean Int interface passed.\n")
    stream.write("- No declaration-level certificate was invented; future integer users retain operation-level correspondence obligations.\n")
    stream.write("- Coverage is now **29 / 357 files** and **252 / 2439 declarations**, with zero validation debt.\n")
PY
stage_end=$(now_ns)
record_stage publication "$stage_start" "$stage_end" PASS FRESH true
cp "$timings" "$publish_dir/stage_timings.jsonl"

(cd "$REPO_ROOT" && git diff --check)
echo "util/int.v: ACCEPTED_V06_FILE"
echo "fresh work directory: $work"
