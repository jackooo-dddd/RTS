#!/bin/zsh
# Fresh prepare/check for analysis/abstract/restricted_supply/busy_sbf.v (Rank 78).
#   prepare: source acquisition, Lean build, Lean audit, export, Rocq import
#   check:   certificate DAG (re-bound sbf/pred + abstract/definitions chains
#            plus BusySbfCorrespondence), type audits, assumption audit
# Usage: validate_analysis_abstract_restricted_supply_busy_sbf.sh [prepare|check|all]
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/analysis_abstract_restricted_supply_busy_sbf_final"
typeset absdef="$PWD/Validation/.work/experiments/analysis_abstract_definitions"
typeset pred="$PWD/Validation/.work/experiments/analysis_sbf_pred"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/analysis_abstract_restricted_supply_busy_sbf"
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
  [[ ! -e "$work" ]] || { print "BUSYSBF_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  typeset PIPE=Validation/planning/v06_pipeline
  [[ "$(sha "$absdef/olean/Prosa/Analysis/Abstract/Definitions.olean")" == "$(jq -r .production_olean_sha256 $PIPE/analysis_abstract_definitions_module_manifest.json)" ]]
  [[ "$(sha "$pred/olean/Prosa/Analysis/Definitions/Sbf/Pred.olean")" == "$(jq -r .production_olean_sha256 $PIPE/analysis_sbf_pred_module_manifest.json)" ]]
  mkdir -p "$work"/{olean,imported,certificates}
  : > "$timing"
  typeset t0=$SECONDS

  # Source: union of the two accepted source closures (shared files are
  # byte-identical) + pinned busy_sbf.v.
  cp -R "$absdef/source" "$work/source"
  ( cd "$pred/source" && find . -type f \( -name '*.vo' -o -name '*.v' \) ) | while read -r f; do
    if [[ -e "$work/source/$f" ]]; then
      cmp -s "$pred/source/$f" "$work/source/$f" || { print "BUSYSBF_SOURCE_CONFLICT: $f" >&2; exit 1; }
    else
      mkdir -p "$work/source/${f:h}"; cp "$pred/source/$f" "$work/source/$f"
    fi
  done
  mkdir -p "$work/source/analysis/abstract/restricted_supply"
  cp "$source_root/analysis/abstract/restricted_supply/busy_sbf.v" "$work/source/analysis/abstract/restricted_supply/busy_sbf.v"
  ( cd "$work/source"; ulimit -s 65520
    opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa analysis/abstract/restricted_supply/busy_sbf.v ) > "$work/source_build.log" 2>&1
  opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
    "$project/$fixtures/BusySbfTypeFingerprintProbe.v" > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  # Lean: union of the two accepted olean closures + fresh BusySbf and
  # interface builds.
  cp -R "$absdef/olean/." "$work/olean/"
  ( cd "$pred/olean" && find . -name '*.olean' ) | while read -r f; do
    if [[ -e "$work/olean/$f" ]]; then
      cmp -s "$pred/olean/$f" "$work/olean/$f" || { print "BUSYSBF_OLEAN_CONFLICT: $f" >&2; exit 1; }
    else
      mkdir -p "$work/olean/${f:h}"; cp "$pred/olean/$f" "$work/olean/$f"
    fi
  done
  rm -rf "$work/olean/Validation"
  mkdir -p "$work/olean/Prosa/Analysis/Abstract/RestrictedSupply" "$work/olean/Validation/fixtures/translation_order"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Analysis/Abstract/RestrictedSupply/BusySbf.olean" \
    Prosa/Analysis/Abstract/RestrictedSupply/BusySbf.lean > "$work/lean_build.log" 2>&1
  for module in ScheduleComputationInterface ServiceComputationInterface SupplyComputationInterface \
      BigcatComputationInterface ArrivalSequenceComputationInterface PredExportInterface \
      AbstractDefinitionsComputationInterface BusySbfComputationInterface; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}.olean" \
      "$fixtures/${module}.lean" > "$work/${module}_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/BusySbfLeanTypeAudit.lean" > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/analysis_abstract_restricted_supply_busy_sbf_export_config.json \
    --output "$work/imported/BusySbf.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  print -r -- 'From LeanImport Require Import Lean.
Lean Import "BusySbf.out".' > "$work/imported/ImportedBusySbf.v"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedBusySbf; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "BUSYSBF_PREPARE_PASS: $(wc -l < "$work/imported/BusySbf.out") export lines, $(wc -c < "$work/imported/BusySbf.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedBusySbf.vo" ]]
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
      ServiceBaseAdapter ServiceNatBoolOperations ServiceIntervalOperations ServiceScheduleOperations \
      AbstractDefinitionsBaseAdapter AbstractDefinitionsNatBoolOperations AbstractDefinitionsIntervalOperations \
      AbstractDefinitionsClasses AbstractDefinitionsOperations AbstractDefinitionsArrivalOperations \
      AbstractDefinitionsTaskOperations AbstractDefinitionsPendingOperations AbstractDefinitionsSums \
      AbstractDefinitionsLogical AbstractDefinitionsBusyInterval \
      BusySbfCorrespondence BusySbfAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "BUSYSBF_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/BusySbfImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/busy_sbf_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/busy_sbf_assumption_config.json" \
    --log certificates/BusySbfAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "BUSYSBF_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
