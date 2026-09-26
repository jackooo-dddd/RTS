#!/bin/zsh
# Fresh prepare/check for model/task/jitter.v (Rank 77).
#   prepare: source acquisition, Lean build, Lean audit, export, Rocq import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_model_task_jitter.sh [prepare|check|all]
# Publication is a separate step: publish_model_task_jitter.py.
#
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/model_task_jitter_final"
typeset concept="$PWD/Validation/.work/experiments/model_task_concept"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/model_task_jitter"
typeset rjitter="$PWD/Validation/.work/experiments/model_readiness_jitter_final"
typeset timing="$work/stage_timing.tsv"
typeset source_root
source_root="$(bash Validation/scripts/ensure_pinned_v06_source.sh)"

sha() { shasum -a 256 "$1" | awk '{print $1}'; }
stamp() { print -r -- "$1	$2	$3" >> "$timing"; }
rocq_c() {
  opam exec --switch=rocq93rc1 -- rocq c \
    -R "$work/source" prosa \
    -Q "$importer" LeanImport -I "$importer" \
    -Q "$work/imported" FoundationImported \
    -Q "$work/certificates" FoundationCertificates \
    -Q "$work/pcertificates" TaskJitterCertificates "$@"
}

prepare() {
  [[ ! -e "$work" ]] || { print "TASKJITTER_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/model/task/jitter.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="model/task/jitter.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  [[ "$(sha "$concept/olean/Prosa/Model/Task/Concept.olean")" == \
    "$(jq -r '.production_olean_sha256' Validation/planning/v06_pipeline/model_task_concept_module_manifest.json)" ]]
  [[ "$(sha "$concept/source/model/task/concept.vo")" == \
    "$(jq -r '.artifact_hashes.source_vo_sha256' Validation/planning/v06_pipeline/model_task_concept_module_manifest.json)" ]]
  mkdir -p "$work"/{olean/Prosa/Model/Task,olean/Validation/fixtures/translation_order,imported,certificates,pcertificates}
  : > "$timing"
  typeset t0=$SECONDS

  [[ "$(sha "$rjitter/olean/Prosa/Model/Readiness/Jitter.olean")" == \
    "$(jq -r '.production_olean_sha256' Validation/planning/v06_pipeline/model_readiness_jitter_module_manifest.json)" ]]
  cp -R "$concept/source" "$work/source"
  mkdir -p "$work/source/model/readiness"
  cp "$source_root/util/tactics.v" "$source_root/util/nat.v" "$work/source/util/"
  cp "$source_root/model/readiness/jitter.v" "$work/source/model/readiness/jitter.v"
  cp "$source_root/model/task/jitter.v" "$work/source/model/task/jitter.v"
  ( cd "$work/source"
    patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-util-tactics.patch"
    patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-model-readiness-jitter.patch" )
  ( cd "$work/source"; ulimit -s 65520
    for f in util/tactics.v util/nat.v model/readiness/jitter.v model/task/jitter.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_build.log" 2>&1
  opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
    "$project/$fixtures/TaskJitterTypeFingerprintProbe.v" > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  cp -R "$concept/olean/Prosa/." "$work/olean/Prosa/"
  mkdir -p "$work/olean/Prosa/Model/Readiness"
  cp "$rjitter/olean/Prosa/Model/Readiness/Jitter.olean" "$work/olean/Prosa/Model/Readiness/"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Model/Task/Jitter.olean" \
    Prosa/Model/Task/Jitter.lean > "$work/lean_build.log" 2>&1
  lean -DautoImplicit=false -R "$PWD" "$fixtures/TaskJitterLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/model_task_jitter_export_config.json \
    --output "$work/imported/TaskJitter.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  cp "$project/$certs/ImportedTaskJitter.v" "$work/imported/"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedTaskJitter; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "TASKJITTER_PREPARE_PASS: $(wc -l < "$work/imported/TaskJitter.out") export lines, $(wc -c < "$work/imported/TaskJitter.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedTaskJitter.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates pcertificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "TASKJITTER_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  cp "$project/$certs"/*.v certificates/
  for m in TaskJitterBaseAdapter TaskJitterCorrespondence TaskJitterAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "TASKJITTER_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/TaskJitterImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/task_jitter_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/task_jitter_assumption_config.json" \
    --log certificates/TaskJitterAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "TASKJITTER_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
