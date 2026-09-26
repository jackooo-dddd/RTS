#!/bin/zsh
# Fresh prepare/check for analysis/facts/model/task_arrivals.v (Rank 91).
#   prepare: source acquisition, Lean build, Lean audit, export, Rocq import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_analysis_facts_model_task_arrivals.sh [prepare|check|all]
# Publication is a separate step: publish_analysis_facts_model_task_arrivals.py.
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
typeset work="$PWD/Validation/.work/experiments/analysis_facts_model_task_arrivals_final"
typeset farr="$PWD/Validation/.work/experiments/analysis_facts_behavior_arrivals_final"
typeset concept="$PWD/Validation/.work/experiments/model_task_concept"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/analysis_facts_model_task_arrivals"
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
  [[ ! -e "$work" ]] || { print "FTA_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/analysis/facts/model/task_arrivals.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="analysis/facts/model/task_arrivals.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  [[ "$(sha "$farr/olean/Prosa/Analysis/Facts/Behavior/Arrivals.olean")" == \
    "$(jq -r '.production_olean_sha256' Validation/planning/v06_pipeline/analysis_facts_behavior_arrivals_module_manifest.json)" ]]
  [[ "$(sha "$farr/source/FactsArrivalsSemanticSource.vo")" == \
    "$(jq -r '.source_vo_sha256' Validation/planning/v06_pipeline/analysis_facts_behavior_arrivals_module_manifest.json)" ]]
  mkdir -p "$work"/{olean/Validation/fixtures/translation_order,imported,certificates}
  : > "$timing"
  typeset t0=$SECONDS

  # Source: accepted facts/behavior/arrivals closure (its semantic module
  # provides [by_arrival_times]) + pinned rel/supremum + tactics with the
  # approved patch + the proof-independent util/list extraction (as in the
  # accepted priority/definitions run) + extraction of this file.  The
  # proof-heavy import of facts/behavior/arrivals is replaced by its semantic
  # module (recorded in the extraction metadata).
  cp -R "$farr/source" "$work/source"
  cp "$source_root/util/rel.v" "$source_root/util/supremum.v" "$source_root/util/tactics.v" "$work/source/util/"
  ( cd "$work/source" && patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-util-tactics.patch" )
  typeset inv=Validation/planning/v06_dependency/declaration_inventory.csv
  python3 Validation/scripts/extract_v06_semantic_source.py \
    --source-root "$source_root" --source-file util/list.v --module ListSemanticSource \
    --declarations "$(grep -F 'util/list.v' $inv | cut -d, -f2 | paste -sd, -)" \
    --computational "$(grep -F 'util/list.v' $inv | awk -F, '$4=="Definition"||$4=="Fixpoint"{print $2}' | paste -sd, -)" \
    --elaborated-evidence Validation/planning/v06_dependency/declaration_type_evidence.json \
    --qualified-prefix prosa.util.list \
    --output "$work/source/util/list.v" --metadata "$work/list_extraction.json" > "$work/list_extraction.log"
  python3 Validation/scripts/extract_v06_semantic_source.py \
    --source-root "$source_root" --source-file analysis/facts/model/task_arrivals.v \
    --module FactsTaskArrivalsSemanticSource \
    --declarations "$(grep -F 'analysis/facts/model/task_arrivals.v' $inv | cut -d, -f2 | paste -sd, -)" \
    --drop-import "Require Export prosa.analysis.facts.behavior.arrivals." \
    --add-import "From mathcomp Require Import path." \
    --add-import "Require Import prosa.util.notation prosa.util.list prosa.FactsArrivalsSemanticSource." \
    --add-import "Import ListSemanticSource FactsArrivalsSemanticSource." \
    --elaborated-evidence Validation/planning/v06_dependency/declaration_type_evidence.json \
    --qualified-prefix prosa.analysis.facts.model.task_arrivals \
    --output "$work/source/FactsTaskArrivalsSemanticSource.v" --metadata "$work/source_extraction.json" \
    > "$work/source_extraction.log"
  cp "$project/$fixtures/FactsTaskArrivalsStatementProbe.v" "$work/source/"
  ( cd "$work/source"; ulimit -s 65520
    for f in util/tactics.v util/rel.v util/supremum.v util/list.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_build.log" 2>&1
  ( cd "$work/source"; ulimit -s 65520
    for f in FactsTaskArrivalsSemanticSource.v FactsTaskArrivalsStatementProbe.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  cp -R "$farr/olean/Prosa" "$work/olean/Prosa"
  mkdir -p "$work/olean/Prosa/Analysis/Facts/Model"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Analysis/Facts/Model/TaskArrivals.olean" \
    Prosa/Analysis/Facts/Model/TaskArrivals.lean > "$work/lean_build.log" 2>&1
  for module in Bigcat ArrivalSequence Arrivals FactsTaskArrivals; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
      "$fixtures/${module}ComputationInterface.lean" > "$work/${module}_interface_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/FactsTaskArrivalsLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/analysis_facts_model_task_arrivals_export_config.json \
    --output "$work/imported/FactsTaskArrivals.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  cp "$project/$certs/ImportedFactsTaskArrivals.v" "$work/imported/"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedFactsTaskArrivals; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "FTA_PREPARE_PASS: $(wc -l < "$work/imported/FactsTaskArrivals.out") export lines, $(wc -c < "$work/imported/FactsTaskArrivals.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedFactsTaskArrivals.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates pcertificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "FTA_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  cp "$project/$certs"/*.v certificates/
  for m in ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence \
      ArrivalsCorrespondence \
      JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations \
      FactsTaskArrivalsCorrespondence FactsTaskArrivalsAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "FTA_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/FactsTaskArrivalsImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/facts_task_arrivals_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/facts_task_arrivals_assumption_config.json" \
    --log certificates/FactsTaskArrivalsAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "FTA_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
