#!/bin/zsh
# Fresh prepare/check for analysis/facts/model/uniprocessor.v (Rank 70).
#   prepare: source acquisition, Lean build, Lean audit, export, Rocq import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_analysis_facts_model_uniprocessor.sh [prepare|check|all]
# Publication is a separate step: publish_analysis_facts_model_uniprocessor.py.
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/analysis_facts_model_uniprocessor_final"
typeset platform="$PWD/Validation/.work/experiments/model_processor_platform_properties"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/analysis_facts_model_uniprocessor"
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
  [[ ! -e "$work" ]] || { print "UNI_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/analysis/facts/model/uniprocessor.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="analysis/facts/model/uniprocessor.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  typeset pm=Validation/planning/v06_pipeline/model_processor_platform_properties_module_manifest.json
  [[ "$(sha "$platform/olean/Prosa/Model/Processor/PlatformProperties.olean")" == "$(jq -r '.artifact_hashes.production_olean' $pm)" ]]
  [[ "$(sha "$platform/source/model/processor/platform_properties.vo")" == "$(jq -r '.artifact_hashes.source_vo' $pm)" ]]
  mkdir -p "$work"/{olean/Prosa/Analysis/Facts/Model,olean/Validation/fixtures/translation_order,imported,certificates}
  : > "$timing"
  typeset t0=$SECONDS

  # Source: accepted platform_properties closure (verified cache) + pinned
  # util/tactics.v and analysis/facts/model/uniprocessor.v with their audited
  # proof-only compatibility patches.
  cp -R "$platform/source" "$work/source"
  mkdir -p "$work/source/analysis/facts/model"
  cp "$source_root/util/tactics.v" "$work/source/util/"
  cp "$source_root/analysis/facts/model/uniprocessor.v" "$work/source/analysis/facts/model/"
  ( cd "$work/source"
    patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-util-tactics.patch"
    patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-analysis-facts-model-uniprocessor.patch" )
  ( cd "$work/source"; ulimit -s 65520
    for f in util/tactics.v analysis/facts/model/uniprocessor.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_build.log" 2>&1
  opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
    "$project/$fixtures/UniprocessorSourceTypeAudit.v" > "$work/source_type_audit.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  # Lean: accepted platform_properties olean closure + fresh Uniprocessor and interface builds.
  cp -R "$platform/olean/Prosa/." "$work/olean/Prosa/"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Analysis/Facts/Model/Uniprocessor.olean" \
    Prosa/Analysis/Facts/Model/Uniprocessor.lean > "$work/lean_build.log" 2>&1
  for module in Schedule Service Supply PlatformProperties Uniprocessor; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
      "$fixtures/${module}ComputationInterface.lean" > "$work/${module}_interface_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/UniprocessorLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/analysis_facts_model_uniprocessor_export_config.json \
    --output "$work/imported/Uniprocessor.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  print -r -- 'From LeanImport Require Import Lean.
Lean Import "Uniprocessor.out".' > "$work/imported/ImportedUniprocessor.v"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedUniprocessor; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "UNI_PREPARE_PASS: $(wc -l < "$work/imported/Uniprocessor.out") export lines, $(wc -c < "$work/imported/Uniprocessor.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedUniprocessor.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
  done
  cp "$project/$certs"/*.v certificates/
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence \
      UniPlatformScheduleBaseAdapter UniPlatformScheduleFiniteOperations \
      UniPlatformScheduleCorrespondence UniPlatformProcessorStateCorrespondence \
      UniPlatformPropertiesCorrespondence UniprocessorCorrespondence \
      UniprocessorAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "UNI_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/UniprocessorImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/uniprocessor_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/uniprocessor_assumption_config.json" \
    --log certificates/UniprocessorAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "UNI_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
