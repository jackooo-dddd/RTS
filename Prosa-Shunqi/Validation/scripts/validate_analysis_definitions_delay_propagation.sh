#!/bin/zsh
# Fresh prepare/check for analysis/definitions/delay_propagation.v (Rank 89).
#   prepare: pinned source + audited proof-only patch on the accepted curves and
#            jitter source closures, Check fingerprints, Lean build, export, import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_analysis_definitions_delay_propagation.sh [prepare|check|all]
# Publication is a separate step: publish_analysis_definitions_delay_propagation.py.
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/analysis_definitions_delay_propagation_final"
typeset curves="$PWD/Validation/.work/experiments/model_task_arrival_curves_final"
typeset rjitter="$PWD/Validation/.work/experiments/model_readiness_jitter_final"
typeset tjitter="$PWD/Validation/.work/experiments/model_task_jitter_final"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/analysis_definitions_delay_propagation"
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
  [[ ! -e "$work" ]] || { print "DP_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/analysis/definitions/delay_propagation.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="analysis/definitions/delay_propagation.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  [[ "$(sha "$curves/olean/Prosa/Model/Task/Arrival/Curves.olean")" == "$(manifest model_task_arrival_curves production_olean_sha256)" ]]
  [[ "$(sha "$rjitter/olean/Prosa/Model/Readiness/Jitter.olean")" == "$(manifest model_readiness_jitter production_olean_sha256)" ]]
  [[ "$(sha "$tjitter/olean/Prosa/Model/Task/Jitter.olean")" == "$(manifest model_task_jitter production_olean_sha256)" ]]
  mkdir -p "$work"/{olean/Validation/fixtures/translation_order,imported,certificates}
  : > "$timing"
  typeset t0=$SECONDS

  # Source: accepted curves closure + the accepted task/readiness jitter
  # sources (pinned, with their approved patches) + pinned delay_propagation.v
  # with the audited proof-only patch.
  cp -R "$curves/source" "$work/source"
  mkdir -p "$work/source/model/readiness" "$work/source/analysis/definitions"
  cp "$source_root/util/tactics.v" "$source_root/util/nat.v" "$work/source/util/"
  cp "$source_root/model/readiness/jitter.v" "$work/source/model/readiness/jitter.v"
  cp "$source_root/model/task/jitter.v" "$work/source/model/task/jitter.v"
  cp "$source_root/analysis/definitions/delay_propagation.v" "$work/source/analysis/definitions/delay_propagation.v"
  ( cd "$work/source"
    patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-util-tactics.patch"
    patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-model-readiness-jitter.patch"
    patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-analysis-definitions-delay-propagation.patch" )
  ( cd "$work/source"; ulimit -s 65520
    for f in util/tactics.v util/nat.v model/readiness/jitter.v model/task/jitter.v \
        analysis/definitions/delay_propagation.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_build.log" 2>&1
  opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
    "$project/$fixtures/DelayPropagationTypeFingerprintProbe.v" > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  cp -R "$curves/olean/Prosa" "$work/olean/Prosa"
  mkdir -p "$work/olean/Prosa/Model/Readiness" "$work/olean/Prosa/Analysis/Definitions"
  cp "$rjitter/olean/Prosa/Model/Readiness/Jitter.olean" "$work/olean/Prosa/Model/Readiness/"
  cp "$tjitter/olean/Prosa/Model/Task/Jitter.olean" "$work/olean/Prosa/Model/Task/"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Analysis/Definitions/DelayPropagation.olean" \
    Prosa/Analysis/Definitions/DelayPropagation.lean > "$work/lean_build.log" 2>&1
  for module in Bigcat ArrivalSequence Arrivals DelayPropagation; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
      "$fixtures/${module}ComputationInterface.lean" > "$work/${module}_interface_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/DelayPropagationLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/analysis_definitions_delay_propagation_export_config.json \
    --output "$work/imported/DelayPropagation.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  cp "$project/$certs/ImportedDelayPropagation.v" "$work/imported/"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedDelayPropagation; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "DP_PREPARE_PASS: $(wc -l < "$work/imported/DelayPropagation.out") export lines, $(wc -c < "$work/imported/DelayPropagation.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedDelayPropagation.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "DP_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  cp "$project/$certs"/*.v certificates/
  for m in ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence \
      ArrivalsCorrespondence \
      DelayPropagationCorrespondence DelayPropagationAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "DP_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/DelayPropagationImportedTypeAudit.v" > imported_type_audit.log 2>&1
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/delay_propagation_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/delay_propagation_assumption_config.json" \
    --log certificates/DelayPropagationAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "DP_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
