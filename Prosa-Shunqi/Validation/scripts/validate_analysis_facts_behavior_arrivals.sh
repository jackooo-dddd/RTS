#!/bin/zsh
# Fresh prepare/check for analysis/facts/behavior/arrivals.v (Rank 82).
#   prepare: source acquisition, Lean build, Lean audit, export, Rocq import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_analysis_facts_behavior_arrivals.sh [prepare|check|all]
# Publication is a separate step: publish_analysis_facts_behavior_arrivals.py.
#
# Source binding: the lemmas' proofs need util lemmas unavailable in the
# accepted validation-only util/all closure, so the pinned file is bound via
# extract_v06_semantic_source.py (statement Prop definitions + byte-identical
# by_arrival_times), checked against the authoritative elaborated types.
#
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/analysis_facts_behavior_arrivals_final"
typeset concept="$PWD/Validation/.work/experiments/model_task_concept"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/analysis_facts_behavior_arrivals"
typeset arrivals="$PWD/Validation/.work/experiments/model_task_arrivals_final"
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
    -Q "$work/pcertificates" FactsArrivalsCertificates "$@"
}

prepare() {
  [[ ! -e "$work" ]] || { print "FARRIVALS_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/analysis/facts/behavior/arrivals.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="analysis/facts/behavior/arrivals.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  [[ "$(sha "$concept/olean/Prosa/Model/Task/Concept.olean")" == \
    "$(jq -r '.production_olean_sha256' Validation/planning/v06_pipeline/model_task_concept_module_manifest.json)" ]]
  [[ "$(sha "$concept/source/model/task/concept.vo")" == \
    "$(jq -r '.artifact_hashes.source_vo_sha256' Validation/planning/v06_pipeline/model_task_concept_module_manifest.json)" ]]
  mkdir -p "$work"/{olean/Prosa/Model/Task,olean/Validation/fixtures/translation_order,imported,certificates,pcertificates}
  : > "$timing"
  typeset t0=$SECONDS

  [[ "$(sha "$arrivals/olean/Prosa/Model/Task/Arrivals.olean")" == \
    "$(jq -r '.production_olean_sha256' Validation/planning/v06_pipeline/model_task_arrivals_module_manifest.json)" ]]
  cp -R "$arrivals/source" "$work/source"
  typeset inv=Validation/planning/v06_dependency/declaration_inventory.csv
  python3 Validation/scripts/extract_v06_semantic_source.py \
    --source-root "$source_root" --source-file analysis/facts/behavior/arrivals.v \
    --module FactsArrivalsSemanticSource \
    --declarations "$(grep -F 'analysis/facts/behavior/arrivals.v' $inv | cut -d, -f2 | paste -sd, -)" \
    --computational by_arrival_times \
    --elaborated-evidence Validation/planning/v06_dependency/declaration_type_evidence.json \
    --qualified-prefix prosa.analysis.facts.behavior.arrivals \
    --add-import "From mathcomp Require Import path." --add-import "Require Import prosa.util.notation." \
    --output "$work/source/FactsArrivalsSemanticSource.v" --metadata "$work/source_extraction.json" \
    > "$work/source_extraction.log"
  cp "$project/$fixtures/FactsArrivalsStatementProbe.v" "$work/source/"
  ( cd "$work/source"; ulimit -s 65520
    for f in FactsArrivalsSemanticSource.v FactsArrivalsStatementProbe.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  cp -R "$arrivals/olean/Prosa/." "$work/olean/Prosa/"
  mkdir -p "$work/olean/Prosa/Analysis/Facts/Behavior"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Analysis/Facts/Behavior/Arrivals.olean" \
    Prosa/Analysis/Facts/Behavior/Arrivals.lean > "$work/lean_build.log" 2>&1
  for module in Bigcat ArrivalSequence Arrivals Schedule Service FactsArrivals; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
      "$fixtures/${module}ComputationInterface.lean" > "$work/${module}_interface_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/FactsArrivalsLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/analysis_facts_behavior_arrivals_export_config.json \
    --output "$work/imported/FactsArrivals.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  cp "$project/$certs/ImportedFactsArrivals.v" "$work/imported/"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedFactsArrivals; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "FARRIVALS_PREPARE_PASS: $(wc -l < "$work/imported/FactsArrivals.out") export lines, $(wc -c < "$work/imported/FactsArrivals.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedFactsArrivals.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates pcertificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "FARRIVALS_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  cp "$project/$certs"/*.v certificates/
  for m in ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence \
      ArrivalsCorrespondence \
      JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations \
      JitterSvcScheduleOperations JitterSvcJobOperations \
      FactsArrivalsCorrespondence FactsArrivalsAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "FARRIVALS_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/FactsArrivalsImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/facts_arrivals_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/facts_arrivals_assumption_config.json" \
    --log certificates/FactsArrivalsAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "FARRIVALS_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
