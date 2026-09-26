#!/bin/zsh
# Fresh prepare/check for analysis/facts/tdma.v (Rank 83).
#   prepare: semantic source extraction + fingerprints, Lean build, export, Rocq import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_analysis_facts_tdma.sh [prepare|check|all]
# Publication is a separate step: publish_analysis_facts_tdma.py.
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/analysis_facts_tdma_final"
typeset tdma="$PWD/Validation/.work/experiments/model_schedule_tdma_final"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/analysis_facts_tdma"
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
  [[ ! -e "$work" ]] || { print "FTDMA_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/analysis/facts/tdma.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="analysis/facts/tdma.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  [[ "$(sha "$tdma/olean/Prosa/Model/Schedule/Tdma.olean")" == \
    "$(jq -r '.production_olean_sha256' Validation/planning/v06_pipeline/model_schedule_tdma_module_manifest.json)" ]]
  [[ "$(sha "$tdma/source/model/schedule/tdma.vo")" == \
    "$(jq -r '.source_vo_sha256' Validation/planning/v06_pipeline/model_schedule_tdma_module_manifest.json)" ]]
  mkdir -p "$work"/{olean/Validation/fixtures/translation_order,imported,certificates}
  : > "$timing"
  typeset t0=$SECONDS

  # Source: accepted TDMA source closure (verified .vo) + proof-independent
  # semantic extraction of the pinned facts file.
  cp -R "$tdma/source" "$work/source"
  typeset inv=Validation/planning/v06_dependency/declaration_inventory.csv
  python3 Validation/scripts/extract_v06_semantic_source.py \
    --source-root "$source_root" --source-file analysis/facts/tdma.v \
    --module FactsTdmaSemanticSource \
    --declarations "$(grep -F 'analysis/facts/tdma.v' $inv | cut -d, -f2 | paste -sd, -)" \
    --elaborated-evidence Validation/planning/v06_dependency/declaration_type_evidence.json \
    --qualified-prefix prosa.analysis.facts.tdma \
    --add-import "Require Import prosa.util.notation." --printer-repair "{setTask}={set Task}" \
    --output "$work/source/FactsTdmaSemanticSource.v" --metadata "$work/source_extraction.json" \
    > "$work/source_extraction.log"
  cp "$project/$fixtures/FactsTdmaStatementProbe.v" "$work/source/"
  ( cd "$work/source"; ulimit -s 65520
    for f in FactsTdmaSemanticSource.v FactsTdmaStatementProbe.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  cp -R "$tdma/olean/Prosa" "$work/olean/Prosa"
  mkdir -p "$work/olean/Prosa/Analysis/Facts"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Analysis/Facts/Tdma.olean" \
    Prosa/Analysis/Facts/Tdma.lean > "$work/lean_build.log" 2>&1
  for module in Schedule Service Tdma FactsTdma; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
      "$fixtures/${module}ComputationInterface.lean" > "$work/${module}_interface_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/FactsTdmaLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/analysis_facts_tdma_export_config.json \
    --output "$work/imported/FactsTdma.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  cp "$project/$certs/ImportedFactsTdma.v" "$work/imported/"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedFactsTdma; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "FTDMA_PREPARE_PASS: $(wc -l < "$work/imported/FactsTdma.out") export lines, $(wc -c < "$work/imported/FactsTdma.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedFactsTdma.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "FTDMA_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  cp "$project/$certs"/*.v certificates/
  for m in FtdmaBaseAdapter FtdmaArithmeticAdapter FtdmaSeqsetAdapter FtdmaPolicyAdapter \
      FtdmaValidityCorrespondence FtdmaNumericCorrespondence \
      FactsTdmaCorrespondence FactsTdmaAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "FTDMA_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/FactsTdmaImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/facts_tdma_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/facts_tdma_assumption_config.json" \
    --log certificates/FactsTdmaAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "FTDMA_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
