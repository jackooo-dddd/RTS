#!/bin/zsh
# Fresh prepare/check for implementation/definitions/maximal_arrival_sequence.v (Rank 92).
#   prepare: pinned supremum.v + maximal_arrival_sequence.v (byte-identical) on the accepted curves
#            source closure, Check fingerprints, Lean build, export, Rocq import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_implementation_definitions_maximal_arrival_sequence.sh [prepare|check|all]
# Publication is a separate step: publish_implementation_definitions_maximal_arrival_sequence.py.
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/implementation_definitions_maximal_arrival_sequence_final"
typeset curves="$PWD/Validation/.work/experiments/model_task_arrival_curves_final"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/implementation_definitions_maximal_arrival_sequence"
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
    -Q "$work/certificates" FoundationCertificates "$@"
}

prepare() {
  [[ ! -e "$work" ]] || { print "MAS_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/implementation/definitions/maximal_arrival_sequence.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="implementation/definitions/maximal_arrival_sequence.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  [[ "$(sha "$curves/olean/Prosa/Model/Task/Arrival/Curves.olean")" == \
    "$(jq -r '.production_olean_sha256' Validation/planning/v06_pipeline/model_task_arrival_curves_module_manifest.json)" ]]
  [[ "$(sha "$curves/source/model/task/arrival/curves.vo")" == \
    "$(jq -r '.source_vo_sha256' Validation/planning/v06_pipeline/model_task_arrival_curves_module_manifest.json)" ]]
  mkdir -p "$work"/{olean/Validation/fixtures/translation_order,imported,certificates}
  : > "$timing"
  typeset t0=$SECONDS

  cp -R "$curves/source" "$work/source"
  mkdir -p "$work/source/implementation/definitions"
  cp "$source_root/util/supremum.v" "$work/source/util/supremum.v"
  cp "$source_root/implementation/definitions/maximal_arrival_sequence.v" "$work/source/implementation/definitions/"
  ( cd "$work/source"; ulimit -s 65520
    for f in util/supremum.v implementation/definitions/maximal_arrival_sequence.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_build.log" 2>&1
  opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
    "$project/$fixtures/MaximalArrivalSequenceTypeFingerprintProbe.v" > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  cp -R "$curves/olean/Prosa" "$work/olean/Prosa"
  mkdir -p "$work/olean/Prosa/Implementation/Definitions"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Implementation/Definitions/MaximalArrivalSequence.olean" \
    Prosa/Implementation/Definitions/MaximalArrivalSequence.lean > "$work/lean_build.log" 2>&1
  for module in MaximalArrivalSequence; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
      "$fixtures/${module}ComputationInterface.lean" > "$work/${module}_interface_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/MaximalArrivalSequenceLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/implementation_definitions_maximal_arrival_sequence_export_config.json \
    --output "$work/imported/MaximalArrivalSequence.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  cp "$project/$certs/ImportedMaximalArrivalSequence.v" "$work/imported/"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedMaximalArrivalSequence; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "MAS_PREPARE_PASS: $(wc -l < "$work/imported/MaximalArrivalSequence.out") export lines, $(wc -c < "$work/imported/MaximalArrivalSequence.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedMaximalArrivalSequence.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "MAS_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  cp "$project/$certs"/*.v certificates/
  for m in JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations \
      MaximalArrivalSequenceCorrespondence MaximalArrivalSequenceAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "MAS_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/MaximalArrivalSequenceImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/mas_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/mas_assumption_config.json" \
    --log certificates/MaximalArrivalSequenceAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "MAS_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
