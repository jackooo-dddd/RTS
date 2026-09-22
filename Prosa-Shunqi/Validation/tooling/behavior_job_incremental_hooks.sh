#!/usr/bin/env bash

VALIDATION_PREPARE_INPUTS=(
  "$VALIDATION_ROOT/tooling/behavior_job_incremental_descriptor.json"
  "$VALIDATION_ROOT/tooling/behavior_job_export_config.json"
  "$VALIDATION_ROOT/tooling/behavior_job_incremental_hooks.sh"
  "$VALIDATION_ROOT/scripts/run_incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/incremental_validation.sh"
  "$VALIDATION_ROOT/scripts/common/validation_common.sh"
)

VALIDATION_CHECK_INPUTS=(
  "$VALIDATION_ROOT/scripts/audit_assumptions.py"
  "$VALIDATION_ROOT/certificates/common/PropSPropFoundation.v"
  "$VALIDATION_ROOT/certificates/common/JobEqTypeAdapter.v"
  "$VALIDATION_ROOT/certificates/foundation_slice_1/FoundationTimeCertificate.v"
  "$VALIDATION_ROOT/certificates/behavior_job/JobCorrespondence.v"
  "$VALIDATION_ROOT/certificates/behavior_job/JobTypeAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_job/JobAssumptionAudit.v"
  "$VALIDATION_ROOT/certificates/behavior_job/job_assumption_config.json"
)

validation_prepare_lean_build() {
  jq -e '.status == "PASS" and
    .coverage.accepted_files == 21 and
    .coverage.accepted_declarations == 204 and
    .coverage.translated_but_not_certified == 0' \
    "$VALIDATION_ROOT/planning/v06_pipeline/util_all_module_status.json" >/dev/null
  jq -e '.FILE_DAG_READY == true and .public_declarations == 5' \
    "$VALIDATION_ROOT/planning/v06_pipeline/behavior_job_selection.json" >/dev/null
  if rg -n '\b(sorry|axiom|unsafe)\b' \
      "$PROJECT_ROOT/Prosa/Behavior/Job.lean"; then
    echo "forbidden production proof escape" >&2
    return 1
  fi
  local modules=(
    Tactics Notation Rel Seqset Subadditivity Supremum Nat UnitGrowth
    SearchArg List Sum Epsilon Bigop Setoid Poet Bigcat Minmax Div_mod
    Nondecreasing All
  )
  local module
  for module in "${modules[@]}"; do
    validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Util/$module" \
      > "$VALIDATION_RUN_LOG/fresh_${module}.log" 2>&1
  done
  validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Behavior/Time" \
    > "$VALIDATION_RUN_LOG/fresh_Time.log" 2>&1
  validation_compile_lean_module "$VALIDATION_PREPARED" "Prosa/Behavior/Job" \
    > "$VALIDATION_RUN_LOG/fresh_Job.log" 2>&1
  lean -DautoImplicit=false -R "$PROJECT_ROOT" \
    "$VALIDATION_ROOT/fixtures/translation_order/LeanJobAudit.lean" \
    > "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" 2>&1
  cp "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    "$VALIDATION_RUN_LOG/lean_freeze_and_axioms.log"
  python3 "$VALIDATION_ROOT/scripts/audit_lean_axioms.py" \
    --config "$VALIDATION_ROOT/fixtures/translation_order/job_lean_axiom_config.json" \
    --log "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    --output "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    > "$VALIDATION_RUN_LOG/lean_axiom_classifier.log"
  jq -e '(.missing | length) == 0 and (.extra | length) == 0 and
    (.declarations | length) == 5 and
    ([.declarations[] | .status == "PASS" and
      (.unexpected_axioms | length == 0)] | all)' \
    "$VALIDATION_PREPARED/lean_axiom_summary.json" >/dev/null
  python3 - "$VALIDATION_PREPARED/olean" \
    "$VALIDATION_PREPARED/dependency_build_manifest.json" <<'PY'
import hashlib, json, sys
from pathlib import Path

root, output = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
files = sorted(root.rglob("*.olean"))
expected = 22
if len(files) != expected:
    raise SystemExit(f"expected {expected} freshly compiled modules, found {len(files)}")
result = {
    "status": "PASS",
    "mode": "FRESH_ACCEPTED_DEPENDENCY_CLOSURE_PLUS_TARGET",
    "module_count": len(files),
    "modules": {
        str(path.relative_to(root)): {"sha256": sha(path), "bytes": path.stat().st_size}
        for path in files
    },
}
output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
PY
  VALIDATION_STAGE_OUTPUTS=(
    "util_all_olean=$VALIDATION_PREPARED/olean/Prosa/Util/All.olean"
    "time_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Time.olean"
    "job_olean=$VALIDATION_PREPARED/olean/Prosa/Behavior/Job.olean"
    "lean_freeze=$VALIDATION_PREPARED/lean_freeze_and_axioms.log"
    "lean_axiom_summary=$VALIDATION_PREPARED/lean_axiom_summary.json"
    "dependency_build_manifest=$VALIDATION_PREPARED/dependency_build_manifest.json"
  )
}

validation_prepare_source_acquisition() {
  mkdir -p "$VALIDATION_PREPARED/source/util" \
    "$VALIDATION_PREPARED/source/behavior"
  cp "$VALIDATION_ROOT/fixtures/translation_order/source_compat/util/all.v" \
    "$VALIDATION_PREPARED/source/util/all.v"
  cp "$SOURCE_ROOT/behavior/time.v" \
    "$VALIDATION_PREPARED/source/behavior/time.v"
  cp "$SOURCE_ROOT/behavior/job.v" \
    "$VALIDATION_PREPARED/source/behavior/job.v"
  [[ $(validation_sha256 "$VALIDATION_PREPARED/source/behavior/job.v") == \
    f107dc6095d152bdf8b7eeb030b73ba47967cee67806991ed7efe24407a5a752 ]]
  cmp -s "$SOURCE_ROOT/behavior/job.v" \
    "$VALIDATION_PREPARED/source/behavior/job.v"
  cmp -s "$SOURCE_ROOT/behavior/time.v" \
    "$VALIDATION_PREPARED/source/behavior/time.v"
  if rg -n '^(Definition|Class|Record|Structure|Inductive|Variant|Lemma|Theorem|Fact|Remark)\b' \
      "$VALIDATION_PREPARED/source/util/all.v"; then
    echo "Job source compatibility interface unexpectedly declares a symbol" >&2
    return 1
  fi
  ulimit -s 65520
  local source
  for source in util/all.v behavior/time.v behavior/job.v; do
    (cd "$VALIDATION_PREPARED/source" && \
      opam exec --switch="$ROCQ_SWITCH" -- rocq c \
        -R "$VALIDATION_PREPARED/source" prosa "$source") \
      > "$VALIDATION_RUN_LOG/source_$(basename "$source" .v).log" 2>&1
  done
  python3 - "$SOURCE_ROOT" "$VALIDATION_ROOT" "$VALIDATION_PREPARED/source" <<'PY'
import csv, hashlib, json, subprocess, sys
from pathlib import Path

source_root, validation, output_root = map(Path, sys.argv[1:])
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rows = [r for r in csv.DictReader(
    (validation / "planning/v06_dependency/declaration_inventory.csv").open()
) if r["source_file"] == "behavior/job.v"]
if [r["declaration_name"] for r in rows] != [
    "JobType", "work", "JobCost", "JobArrival", "JobDeadline"
]:
    raise SystemExit("authoritative Job declaration inventory changed")
types = json.loads(
    (validation / "planning/v06_dependency/declaration_type_evidence.json").read_text()
)
declarations = {}
for row in rows:
    qname = row["qualified_name"]
    evidence = types.get(qname)
    if evidence is None or evidence["sha256"] != row[
        "final_type_or_type_fingerprint"
    ].removeprefix("rocq-check-sha256:"):
        raise SystemExit(f"elaborated type evidence mismatch: {qname}")
    declarations[row["declaration_name"]] = {
        "qualified_name": qname,
        "kind": row["kind"],
        "source_command_sha256": row["source_command_sha256"],
        "elaborated_type_sha256": evidence["sha256"],
        "normalized_check": evidence["normalized_check"],
    }
result = {
    "status": "PASS",
    "source_commit": subprocess.check_output(
        ["git", "-C", str(source_root), "rev-parse", "HEAD"], text=True
    ).strip(),
    "source_file": "behavior/job.v",
    "authoritative_source_sha256": sha(source_root / "behavior/job.v"),
    "compiled_source_sha256": sha(output_root / "behavior/job.v"),
    "byte_identical_authoritative_source": True,
    "compatibility_interface": "util/all.v",
    "compatibility_interface_sha256": sha(output_root / "util/all.v"),
    "compatibility_interface_declares_no_prosa_symbol": True,
    "declarations": declarations,
}
(output_root / "job_source_acquisition.json").write_text(
    json.dumps(result, indent=2, sort_keys=True) + "\n"
)
PY
  VALIDATION_STAGE_OUTPUTS=(
    "source_compat=$VALIDATION_PREPARED/source/util/all.vo"
    "source_time=$VALIDATION_PREPARED/source/behavior/time.vo"
    "source_job=$VALIDATION_PREPARED/source/behavior/job.vo"
    "source_metadata=$VALIDATION_PREPARED/source/job_source_acquisition.json"
  )
}

validation_prepare_export() {
  "$VALIDATION_ROOT/scripts/export_actual_artifact.sh" \
    --config "$VALIDATION_ROOT/tooling/behavior_job_export_config.json" \
    --output "$VALIDATION_PREPARED/imported/Job.out" \
    --log "$VALIDATION_RUN_LOG/export.log" \
    --metadata "$VALIDATION_PREPARED/imported/job_export_metadata.json"
  VALIDATION_STAGE_OUTPUTS=(
    "export=$VALIDATION_PREPARED/imported/Job.out"
    "export_metadata=$VALIDATION_PREPARED/imported/job_export_metadata.json"
  )
}

validation_prepare_rocq_import() {
  cp "$VALIDATION_ROOT/imported/foundation_slice_1/Time.out" \
    "$VALIDATION_PREPARED/imported/Time.out"
  cp "$VALIDATION_ROOT/imported/foundation_slice_1/ImportedTime.v" \
    "$VALIDATION_PREPARED/imported/ImportedTime.v"
  cp "$VALIDATION_ROOT/fixtures/translation_order/ImportedJob.v" \
    "$VALIDATION_PREPARED/imported/ImportedJob.v"
  ulimit -s 65520
  local module
  for module in ImportedTime ImportedJob; do
    (cd "$VALIDATION_PREPARED/imported" && \
      validation_rocq_compile "$VALIDATION_PREPARED" "${module}.v") \
      > "$VALIDATION_RUN_LOG/import_${module}.log" 2>&1
  done
  VALIDATION_STAGE_OUTPUTS=(
    "time_export=$VALIDATION_PREPARED/imported/Time.out"
    "time_import_source=$VALIDATION_PREPARED/imported/ImportedTime.v"
    "time_import_vo=$VALIDATION_PREPARED/imported/ImportedTime.vo"
    "job_import_source=$VALIDATION_PREPARED/imported/ImportedJob.v"
    "job_import_vo=$VALIDATION_PREPARED/imported/ImportedJob.vo"
  )
}

validation_check_setup() {
  cp -R "$VALIDATION_PREPARED/olean/." "$VALIDATION_PHASE_WORK/olean/"
  cp -R "$VALIDATION_PREPARED/source/." "$VALIDATION_PHASE_WORK/source/"
  cp -R "$VALIDATION_PREPARED/imported/." "$VALIDATION_PHASE_WORK/imported/"
  cp "$VALIDATION_PREPARED/lean_freeze_and_axioms.log" \
    "$VALIDATION_PHASE_WORK/lean_freeze_and_axioms.log"
  cp "$VALIDATION_PREPARED/lean_axiom_summary.json" \
    "$VALIDATION_PHASE_WORK/lean_axiom_summary.json"
}

validation_check_certificate_compile() {
  mkdir -p "$VALIDATION_PHASE_WORK/certificates"
  cp "$VALIDATION_ROOT/certificates/common/PropSPropFoundation.v" \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$VALIDATION_ROOT/certificates/foundation_slice_1/FoundationTimeCertificate.v" \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$VALIDATION_ROOT/certificates/common/JobEqTypeAdapter.v" \
    "$VALIDATION_PHASE_WORK/certificates/"
  cp "$VALIDATION_ROOT/certificates/behavior_job/"{JobCorrespondence,JobTypeAudit,JobAssumptionAudit}.v \
    "$VALIDATION_PHASE_WORK/certificates/"
  local path
  for path in \
      "$VALIDATION_ROOT/certificates/common/JobEqTypeAdapter.v" \
      "$VALIDATION_ROOT/certificates/behavior_job/JobCorrespondence.v" \
      "$VALIDATION_ROOT/certificates/behavior_job/JobTypeAudit.v" \
      "$VALIDATION_ROOT/certificates/behavior_job/JobAssumptionAudit.v"; do
    if rg -n '\b(Admitted|admit|Axiom)\b|\bsorry\b' "$path"; then
      echo "forbidden certificate escape in $path" >&2
      return 1
    fi
  done
  ulimit -s 65520
  local module
  for module in PropSPropFoundation FoundationTimeCertificate \
      JobEqTypeAdapter JobCorrespondence JobTypeAudit JobAssumptionAudit; do
    validation_rocq_compile "$VALIDATION_PHASE_WORK" \
      "$VALIDATION_PHASE_WORK/certificates/${module}.v" \
      > "$VALIDATION_RUN_LOG/rocq_${module}.log" 2>&1
  done
  cp "$VALIDATION_RUN_LOG/rocq_JobAssumptionAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  cp "$VALIDATION_RUN_LOG/rocq_JobTypeAudit.log" \
    "$VALIDATION_PHASE_WORK/certificates/type_audit.log"
  VALIDATION_STAGE_OUTPUTS=(
    "eqtype_adapter_vo=$VALIDATION_PHASE_WORK/certificates/JobEqTypeAdapter.vo"
    "certificate_vo=$VALIDATION_PHASE_WORK/certificates/JobCorrespondence.vo"
    "type_audit_vo=$VALIDATION_PHASE_WORK/certificates/JobTypeAudit.vo"
    "assumption_audit_vo=$VALIDATION_PHASE_WORK/certificates/JobAssumptionAudit.vo"
    "type_audit_log=$VALIDATION_PHASE_WORK/certificates/type_audit.log"
    "assumption_log=$VALIDATION_PHASE_WORK/certificates/assumptions.log"
  )
}

validation_check_assumption_audit() {
  python3 "$VALIDATION_ROOT/scripts/audit_assumptions.py" \
    --config "$VALIDATION_ROOT/certificates/behavior_job/job_assumption_config.json" \
    --log "$VALIDATION_PHASE_WORK/certificates/assumptions.log" \
    --output "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    > "$VALIDATION_RUN_LOG/assumption_classifier.log"
  jq -e '(.certificates | length) == 16 and
    ([.certificates[] | .status == "CERTIFIED" and
      (.semantic_premises | length == 0) and
      (.prop_sprop_foundation | length == 0) and
      (.unexpected | length == 0) and
      (.source_theorem_dependency == false) and
      (.target_theorem_dependency == false)] | all)' \
    "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" >/dev/null
  python3 - "$VALIDATION_ROOT/planning/v06_pipeline/util_all_module_status.json" \
    "$VALIDATION_PHASE_WORK/certificates/baseline_after.json" <<'PY'
import json, sys
from pathlib import Path
source, output = map(Path, sys.argv[1:])
data = json.loads(source.read_text())
ok = (
    data.get("status") == "PASS"
    and data["coverage"]["accepted_files"] == 21
    and data["coverage"]["accepted_declarations"] == 204
    and data["coverage"]["translated_but_not_certified"] == 0
)
output.write_text(json.dumps({
    "status": "PASS" if ok else "FAIL_BASELINE",
    "accepted_files": data["coverage"]["accepted_files"],
    "accepted_declarations": data["coverage"]["accepted_declarations"],
}, indent=2) + "\n")
if not ok:
    raise SystemExit(1)
PY
  [[ -z $(git -C "$REPO_ROOT" status --short -- Prosa-fei) ]]
  VALIDATION_STAGE_OUTPUTS=(
    "assumption_summary=$VALIDATION_PHASE_WORK/certificates/assumption_summary.json"
    "baseline_audit=$VALIDATION_PHASE_WORK/certificates/baseline_after.json"
  )
}

validation_finalize_publication() {
  local publish_dir="$VALIDATION_ROOT/imported/translation_order/job"
  local pipeline_dir="$VALIDATION_ROOT/planning/v06_pipeline"
  local report="$PROJECT_ROOT/Reports/files/behavior/2026-09-22_210645_job.md"
  mkdir -p "$publish_dir" "$(dirname "$report")"
  cp "$VALIDATION_PHASE_WORK/imported/"{Job.out,ImportedJob.v,ImportedJob.vo} \
    "$publish_dir/"
  local module
  for module in JobEqTypeAdapter JobCorrespondence JobTypeAudit JobAssumptionAudit; do
    cp "$VALIDATION_PHASE_WORK/certificates/${module}.vo" \
      "$publish_dir/${module}.vo"
  done
  cp "$VALIDATION_PHASE_WORK/certificates/assumption_summary.json" \
    "$publish_dir/assumption_summary.json"
  cp "$VALIDATION_PHASE_WORK/lean_axiom_summary.json" \
    "$publish_dir/lean_axiom_summary.json"
  cp "$VALIDATION_PHASE_WORK/source/job_source_acquisition.json" \
    "$publish_dir/job_source_acquisition.json"
  python3 - "$PROJECT_ROOT" "$SOURCE_ROOT" "$VALIDATION_PHASE_WORK" \
    "$VALIDATION_PREPARED" "$VALIDATION_PREPARE_EVIDENCE" \
    "$VALIDATION_SNAPSHOT_ID" \
    "$pipeline_dir/util_all_module_status.json" \
    "$pipeline_dir/behavior_job_module_manifest.json" \
    "$pipeline_dir/behavior_job_module_status.json" "$report" <<'PY'
import hashlib, json, subprocess, sys
from datetime import datetime
from pathlib import Path

(project, source, work, prepared, prepare_evidence, snapshot_id,
 previous_path, manifest_out, status_out, report_out) = sys.argv[1:]
project, source, work, prepared, prepare_evidence = map(
    Path, (project, source, work, prepared, prepare_evidence)
)
previous_path, manifest_out, status_out, report_out = map(
    Path, (previous_path, manifest_out, status_out, report_out)
)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
previous = json.loads(previous_path.read_text())
assumptions = json.loads((work / "certificates/assumption_summary.json").read_text())
source_meta = json.loads((work / "source/job_source_acquisition.json").read_text())
lean_axioms = json.loads((work / "lean_axiom_summary.json").read_text())
prepare_run = json.loads(prepare_evidence.read_text())
assert previous["coverage"]["accepted_files"] == 21
assert previous["coverage"]["accepted_declarations"] == 204
assert len(assumptions["certificates"]) == 16
assert all(x["status"] == "CERTIFIED" for x in assumptions["certificates"].values())

bundles = {
    "JobType": ["JobType"],
    "work": ["work_total", "work_source_roundtrip", "work_target_roundtrip"],
    "JobCost": ["JobCost_import", "JobCost_export", "JobCost_source_roundtrip", "JobCost_target_roundtrip"],
    "JobArrival": ["JobArrival_import", "JobArrival_export", "JobArrival_source_roundtrip", "JobArrival_target_roundtrip"],
    "JobDeadline": ["JobDeadline_import", "JobDeadline_export", "JobDeadline_source_roundtrip", "JobDeadline_target_roundtrip"],
}
lean_names = {name: f"Prosa.Behavior.Job.{name}" for name in bundles}
declarations = []
for name, keys in bundles.items():
    records = [assumptions["certificates"][key] for key in keys]
    declarations.append({
        "source_declaration": f"prosa.behavior.job.{name}",
        "lean_declaration": lean_names[name],
        "kind": source_meta["declarations"][name]["kind"],
        "source_command_sha256": source_meta["declarations"][name]["source_command_sha256"],
        "source_elaborated_type_sha256": source_meta["declarations"][name]["elaborated_type_sha256"],
        "semantic_status": "CERTIFIED",
        "certificate_bundle": [record["certificate"] for record in records],
        "semantic_premises": [],
        "prop_sprop_foundation": [],
        "unexpected_assumptions": [],
        "source_theorem_dependency": False,
        "target_theorem_dependency": False,
        "acceptance": "ACCEPTED_V06_TRANSLATION",
    })
manifest = {
    "slice": "TRANSLATION_ORDER_BEHAVIOR_JOB",
    "generated_at": datetime.now().astimezone().isoformat(),
    "source_file": "behavior/job.v",
    "source_commit": subprocess.check_output(
        ["git", "-C", str(source), "rev-parse", "HEAD"], text=True
    ).strip(),
    "source_file_sha256": sha(source / "behavior/job.v"),
    "source_acquisition_sha256": sha(work / "source/job_source_acquisition.json"),
    "production_file": "Prosa/Behavior/Job.lean",
    "production_source_sha256": sha(project / "Prosa/Behavior/Job.lean"),
    "production_olean_sha256": sha(work / "olean/Prosa/Behavior/Job.olean"),
    "export_sha256": sha(work / "imported/Job.out"),
    "import_sha256": sha(work / "imported/ImportedJob.vo"),
    "eqtype_adapter_source_sha256": sha(project / "Validation/certificates/common/JobEqTypeAdapter.v"),
    "eqtype_adapter_vo_sha256": sha(work / "certificates/JobEqTypeAdapter.vo"),
    "certificate_source_sha256": sha(project / "Validation/certificates/behavior_job/JobCorrespondence.v"),
    "certificate_vo_sha256": sha(work / "certificates/JobCorrespondence.vo"),
    "type_audit_vo_sha256": sha(work / "certificates/JobTypeAudit.vo"),
    "assumption_audit_vo_sha256": sha(work / "certificates/JobAssumptionAudit.vo"),
    "lean_axiom_summary_sha256": sha(work / "lean_axiom_summary.json"),
    "assumption_summary_sha256": sha(work / "certificates/assumption_summary.json"),
    "snapshot_id": snapshot_id,
    "prepare_mode": prepare_run["run_mode"],
    "prepare_evidence_sha256": sha(prepare_evidence),
    "declarations": declarations,
    "acceptance": "ACCEPTED_V06_FILE",
}
manifest_out.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
status = {
    "slice": "TRANSLATION_ORDER_BEHAVIOR_JOB",
    "per_file": {
        "behavior/job.v": {
            "public_declarations": 5,
            "translated": 5,
            "proof_clean": 5,
            "certified": 5,
            "certified_without_prop_sprop_foundation": 5,
            "certified_with_prop_sprop_foundation": 0,
            "status": "ACCEPTED_V06_FILE",
        }
    },
    "coverage": {
        "accepted_files": 22,
        "authoritative_files": 357,
        "accepted_declarations": 209,
        "authoritative_declarations": 2439,
        "translated_but_not_certified": 0,
        "deferred_external_boundary": 239,
    },
    "previous_status_sha256": sha(previous_path),
    "snapshot_id": snapshot_id,
    "status": "PASS",
}
status_out.write_text(json.dumps(status, indent=2) + "\n")

report = f"""# behavior/job.v — canonical translation report

First experiment timestamp: **2026-09-22 21:06:45 +08:00**  
Latest accepted validation: **{manifest['generated_at']}**

## Authority and scope

- Official source: Prosa v0.6 commit `{manifest['source_commit']}`.
- Source file: `behavior/job.v` (`{manifest['source_file_sha256']}`).
- Production candidate: `Prosa/Behavior/Job.lean` (`{manifest['production_source_sha256']}`).
- File-DAG prerequisites: accepted `behavior/time.v` and `util/all.v`.
- Public declarations: `JobType`, `work`, `JobCost`, `JobArrival`, `JobDeadline`.

## Translation and representation findings

The source `JobType := eqType` is represented deliberately as a Lean carrier
`Type` plus explicit `[DecidableEq Job]` at every class boundary.  Validation
constructs the target equality decision from MathComp `eqP` and checks the two
decision branches against the actual imported `DecidableEq` datatype.  This is
a representation change, not a claim that `eqType` and `Type` are identical.

`work` and both time-valued fields use the already certified Nat/time
roundtrip.  Rocq 0.6 elaborates each source Class as its sole function field;
Lean uses a one-field structure.  Each class therefore has source→target and
target→source maps, field preservation, and observational roundtrips in both
directions.  Literal function/record equality is neither needed nor claimed.

## Source fidelity and actual artifact

The validator compiled byte-identical official `behavior/time.v` and
`behavior/job.v`.  A validation-only `util/all.v` compatibility interface
exports only MathComp dependencies and declares no Prosa symbol; this avoids
the unrelated Rocq 9.3 stack overflow in the legacy full utility closure.  All
five source command hashes and elaborated type fingerprints are bound in
`job_source_acquisition.json`.

The target was freshly compiled with Lean 4.33.1, exported from the actual
`Prosa.Behavior.Job` `.olean`, and imported using the pinned importer.  Artifact
hashes: `.olean` `{manifest['production_olean_sha256']}`, export
`{manifest['export_sha256']}`, imported `.vo` `{manifest['import_sha256']}`.

## Declaration results

| Declaration | Semantic evidence | Status |
|---|---|---|
| `JobType` | carrier + artifact-local equality-decision correspondence | `CERTIFIED` |
| `work` | total relation and two Nat roundtrips | `CERTIFIED` |
| `JobCost` | constructor/projection correspondence and two observational roundtrips | `CERTIFIED` |
| `JobArrival` | constructor/projection correspondence and two observational roundtrips | `CERTIFIED` |
| `JobDeadline` | constructor/projection correspondence and two observational roundtrips | `CERTIFIED` |

The assumption audit classified all 16 component certificates as
`CERTIFIED`.  Semantic premises, Prop/SProp foundation use, source theorem
self-dependency, target theorem self-dependency, and unexpected assumptions
are all empty/false.  The only reported foundation is the importer's documented
definitional-UIP treatment of imported equality.

## History

- **2026-09-22 21:06:45 +08:00 — selection.** Rank 22 was selected after the
  two direct dependencies were confirmed accepted.  The approved mapping
  required explicit equality evidence at every Job class boundary.
- **2026-09-22 — actual-artifact preflight.** The five Lean candidates compiled
  proof-clean.  Export initially needed the nested projection names generated
  by Lean; after using those exact compiled names, export and Rocq import passed.
- **2026-09-22 — source compatibility finding.** Directly loading the complete
  old `util/all` closure on Rocq 9.3 risks the known `util/list.v` stack overflow.
  The exact Job source was instead compiled unchanged against a declaration-free
  compatibility import surface.  This changes no Job declaration.
- **2026-09-22 — acceptance.** Bidirectional class correspondence and equality
  evidence closed without semantic premises.  Fresh prepare, certificate
  compilation, fail-closed assumption audit, and publication passed.

Final file status: **ACCEPTED_V06_FILE**.
"""
report_out.write_text(report)
PY
  (cd "$REPO_ROOT" && git diff --check)
  VALIDATION_STAGE_OUTPUTS=(
    "module_manifest=$pipeline_dir/behavior_job_module_manifest.json"
    "module_status=$pipeline_dir/behavior_job_module_status.json"
    "canonical_report=$report"
    "published_import=$publish_dir/ImportedJob.vo"
    "published_certificate=$publish_dir/JobCorrespondence.vo"
  )
}
