#!/bin/zsh
# Fresh prepare/check for analysis/facts/model/scheduled.v (Rank 90).
#   prepare: semantic source extraction (the file re-exports the proof-heavy
#            analysis/facts/behavior/arrivals, which is itself bound by
#            extraction; its import is dropped as unused by the statements),
#            statement fingerprints, Lean build, export, Rocq import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_analysis_facts_model_scheduled.sh [prepare|check|all]
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/analysis_facts_model_scheduled_final"
typeset sbf="$PWD/Validation/.work/experiments/analysis_facts_sbf_final"
typeset farr="$PWD/Validation/.work/experiments/analysis_facts_behavior_arrivals_final"
typeset scheduled="$PWD/Validation/.work/experiments/model_schedule_scheduled"
typeset aservice="$PWD/Validation/.work/experiments/analysis_definitions_service"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/analysis_facts_model_scheduled"
typeset timing="$work/stage_timing.tsv"
typeset source_root
source_root="$(bash Validation/scripts/ensure_pinned_v06_source.sh)"

sha() { shasum -a 256 "$1" | awk '{print $1}'; }
stamp() { print -r -- "$1	$2	$3" >> "$timing"; }
manifest() { jq -r ".$2" "Validation/planning/v06_pipeline/$1_module_manifest.json"; }
rocq_c() {
  opam exec --switch=rocq93rc1 -- rocq c \
    -R "$work/source" prosa \
    -Q "$importer" LeanImport -I "$importer" \
    -Q "$work/imported" FoundationImported \
    -Q "$work/certificates" FoundationCertificates "$@"
}

prepare() {
  [[ ! -e "$work" ]] || { print "FSCHED_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/analysis/facts/model/scheduled.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="analysis/facts/model/scheduled.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  [[ "$(sha "$farr/olean/Prosa/Analysis/Facts/Behavior/Arrivals.olean")" == "$(manifest analysis_facts_behavior_arrivals production_olean_sha256)" ]]
  [[ "$(sha "$scheduled/olean/Prosa/Model/Schedule/Scheduled.olean")" == "$(manifest model_schedule_scheduled production_olean_sha256)" ]]
  [[ "$(sha "$aservice/olean/Prosa/Analysis/Definitions/Service.olean")" == "$(manifest analysis_service production_olean_sha256)" ]]
  [[ "$(sha "$farr/olean/Prosa/Model/Processor/PlatformProperties.olean")" == "$(manifest model_processor_platform_properties artifact_hashes.production_olean)" ]]
  mkdir -p "$work"/{olean/Validation/fixtures/translation_order,imported,certificates}
  : > "$timing"
  typeset t0=$SECONDS

  # Source: accepted facts/SBF closure (patched tactics, supply, platform
  # properties) + pinned epsilon / model/schedule/scheduled / analysis/
  # definitions/service (byte-identical) + extraction of this file.
  cp -R "$sbf/source" "$work/source"
  mkdir -p "$work/source/model/schedule" "$work/source/analysis/definitions"
  cp "$source_root/util/epsilon.v" "$work/source/util/"
  cp "$source_root/model/schedule/scheduled.v" "$work/source/model/schedule/"
  cp "$source_root/analysis/definitions/service.v" "$work/source/analysis/definitions/"
  ( cd "$work/source"; ulimit -s 65520
    for f in util/epsilon.v model/schedule/scheduled.v analysis/definitions/service.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_build.log" 2>&1
  typeset inv=Validation/planning/v06_dependency/declaration_inventory.csv
  python3 Validation/scripts/extract_v06_semantic_source.py \
    --source-root "$source_root" --source-file analysis/facts/model/scheduled.v \
    --module FactsScheduledSemanticSource \
    --declarations "$(grep -F 'analysis/facts/model/scheduled.v' $inv | cut -d, -f2 | paste -sd, -)" \
    --type-valued scheduled_at_dec \
    --drop-import "Require Export prosa.analysis.facts.behavior.arrivals." \
    --elaborated-evidence Validation/planning/v06_dependency/declaration_type_evidence.json \
    --qualified-prefix prosa.analysis.facts.model.scheduled \
    --output "$work/source/FactsScheduledSemanticSource.v" --metadata "$work/source_extraction.json" \
    > "$work/source_extraction.log"
  cp "$project/$fixtures/FactsScheduledStatementProbe.v" "$work/source/"
  ( cd "$work/source"; ulimit -s 65520
    for f in FactsScheduledSemanticSource.v FactsScheduledStatementProbe.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  cp -R "$farr/olean/Prosa" "$work/olean/Prosa"
  mkdir -p "$work/olean/Prosa/Model/Schedule" "$work/olean/Prosa/Analysis/Definitions" "$work/olean/Prosa/Analysis/Facts/Model"
  cp "$scheduled/olean/Prosa/Model/Schedule/Scheduled.olean" "$work/olean/Prosa/Model/Schedule/"
  cp "$aservice/olean/Prosa/Analysis/Definitions/Service.olean" "$work/olean/Prosa/Analysis/Definitions/"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Analysis/Facts/Model/Scheduled.olean" \
    Prosa/Analysis/Facts/Model/Scheduled.lean > "$work/lean_build.log" 2>&1
  for module in Bigcat ArrivalSequence Arrivals Schedule Service FactsScheduled; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
      "$fixtures/${module}ComputationInterface.lean" > "$work/${module}_interface_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/FactsScheduledLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/analysis_facts_model_scheduled_export_config.json \
    --output "$work/imported/FactsScheduled.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  cp "$project/$certs/ImportedFactsScheduled.v" "$work/imported/"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedFactsScheduled; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "FSCHED_PREPARE_PASS: $(wc -l < "$work/imported/FactsScheduled.out") export lines, $(wc -c < "$work/imported/FactsScheduled.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedFactsScheduled.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "FSCHED_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  cp "$project/$certs"/*.v certificates/
  for m in ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence \
      JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations \
      JitterSvcScheduleOperations JitterSvcJobOperations \
      FactsScheduledCorrespondence FactsScheduledAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "FSCHED_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/FactsScheduledImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/facts_scheduled_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/facts_scheduled_assumption_config.json" \
    --log certificates/FactsScheduledAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "FSCHED_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
