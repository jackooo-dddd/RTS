#!/bin/zsh
# Fresh prepare/check for analysis/facts/SBF.v (Rank 81).
#   prepare: source acquisition, Lean build, Lean audit, export, Rocq import
#   check:   certificate DAG (re-bound facts/behavior/supply and sbf/pred chains
#            + SbfFactsCorrespondence), type audits, assumption audit
# Usage: validate_analysis_facts_sbf.sh [prepare|check|all]
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/analysis_facts_sbf_final"
typeset fsupply="$PWD/Validation/.work/experiments/analysis_facts_behavior_supply"
typeset pred="$PWD/Validation/.work/experiments/analysis_sbf_pred"
typeset concept="$PWD/Validation/.work/experiments/model_task_concept"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/analysis_facts_sbf"
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
  [[ ! -e "$work" ]] || { print "SBFFACTS_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  typeset PIPE=Validation/planning/v06_pipeline
  [[ "$(sha "$fsupply/source_compat/analysis/facts/behavior/supply.vo")" == "$(jq -r .artifact_hashes.source_vo_sha256 $PIPE/analysis_facts_behavior_supply_module_manifest.json)" ]]
  [[ "$(sha "$fsupply/olean/Prosa/Analysis/Facts/Behavior/Supply.olean")" == "$(jq -r .production_olean_sha256 $PIPE/analysis_facts_behavior_supply_module_manifest.json)" ]]
  [[ "$(sha "$pred/olean/Prosa/Analysis/Definitions/Sbf/Pred.olean")" == "$(jq -r .production_olean_sha256 $PIPE/analysis_sbf_pred_module_manifest.json)" ]]
  [[ "$(sha "$concept/olean/Prosa/Model/Task/Concept.olean")" == "$(jq -r .production_olean_sha256 $PIPE/model_task_concept_module_manifest.json)" ]]
  mkdir -p "$work"/{olean,imported,certificates}
  : > "$timing"
  typeset t0=$SECONDS

  # Source: accepted facts/behavior/supply source closure (its source_compat
  # tree already contains sbf/pred, setoid, tactics) + accepted concept.vo
  # (built on byte-identical behavior/util .vo) + pinned SBF.v with the
  # audited proof-only compatibility patch.
  mkdir -p "$work/source"
  ( cd "$fsupply/source_compat" && find . -type f \( -name '*.vo' -o -name '*.v' \) ! -name '*Probe*' ! -name 'check_*' ! -name 'Check*' ) | while read -r f; do
    mkdir -p "$work/source/${f:h}"; cp "$fsupply/source_compat/$f" "$work/source/$f"
  done
  rm -f "$work/source/analysis/facts/SBF.v" "$work/source/analysis/facts/SBF.glob"
  for f in behavior/all.vo util/all.vo util/notation.vo; do
    cmp -s "$concept/source/$f" "$work/source/$f" || { print "SBFFACTS_SOURCE_CONFLICT: $f" >&2; exit 1; }
  done
  mkdir -p "$work/source/model/task"; cp "$concept/source/model/task/concept.v" "$concept/source/model/task/concept.vo" "$work/source/model/task/"
  cp "$source_root/analysis/facts/SBF.v" "$work/source/analysis/facts/SBF.v"
  ( cd "$work/source" && patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-analysis-facts-sbf.patch" )
  ( cd "$work/source"; ulimit -s 65520
    opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa analysis/facts/SBF.v ) > "$work/source_build.log" 2>&1
  opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
    "$project/$fixtures/SbfFactsTypeFingerprintProbe.v" > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  # Lean: union of the accepted olean closures + fresh SBF facts and
  # interface builds.
  cp -R "$fsupply/olean/." "$work/olean/"
  for dep in "$pred" "$concept"; do
    ( cd "$dep/olean" && find ./Prosa -name '*.olean' ) | while read -r f; do
      if [[ -e "$work/olean/$f" ]]; then
        cmp -s "$dep/olean/$f" "$work/olean/$f" || { print "SBFFACTS_OLEAN_CONFLICT: $f" >&2; exit 1; }
      else
        mkdir -p "$work/olean/${f:h}"; cp "$dep/olean/$f" "$work/olean/$f"
      fi
    done
  done
  rm -rf "$work/olean/Validation"
  mkdir -p "$work/olean/Prosa/Analysis/Facts" "$work/olean/Validation/fixtures/translation_order"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Analysis/Facts/SBF.olean" \
    Prosa/Analysis/Facts/SBF.lean > "$work/lean_build.log" 2>&1
  for module in ScheduleComputationInterface ServiceComputationInterface SupplyComputationInterface \
      PlatformPropertiesComputationInterface FactsBehaviorSupplyComputationInterface \
      BigcatComputationInterface ArrivalSequenceComputationInterface PredExportInterface \
      SbfFactsComputationInterface; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}.olean" \
      "$fixtures/${module}.lean" > "$work/${module}_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/SbfFactsLeanTypeAudit.lean" > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/analysis_facts_sbf_combined_export_config.json \
    --output "$work/imported/SbfFacts.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  print -r -- 'From LeanImport Require Import Lean.
Lean Import "SbfFacts.out".' > "$work/imported/ImportedSbfFacts.v"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedSbfFacts; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "SBFFACTS_PREPARE_PASS: $(wc -l < "$work/imported/SbfFacts.out") export lines, $(wc -c < "$work/imported/SbfFacts.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedSbfFacts.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
  done
  cp "$project/$certs"/*.v certificates/
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
      ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence \
      SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations SupplyScheduleOperations \
      SupplyBaseAdapter SupplyNatBoolOperations SupplyIntervalOperations SupplyCorrespondence \
      PredCorrespondence \
      FsScheduleBaseAdapter FsScheduleFiniteOperations FsScheduleCorrespondence \
      FsProcessorStateCorrespondence FactsSupplyOperationCorrespondence \
      FactsSupplyPlatformPropertiesCorrespondence FactsSupplyStatementCorrespondence \
      SbfFactsCorrespondence SbfFactsAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "SBFFACTS_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/SbfFactsImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/sbf_facts_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/sbf_facts_assumption_config.json" \
    --log certificates/SbfFactsAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "SBFFACTS_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
