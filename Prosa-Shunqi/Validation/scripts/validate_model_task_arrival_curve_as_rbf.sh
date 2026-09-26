#!/bin/zsh
# Fresh prepare/check for model/task/arrival/curve_as_rbf.v (Rank 96).
#   prepare: accepted curves source closure + pinned request_bound_functions.v
#            (byte-identical, .vo checked against its manifest) + extraction of
#            curve_as_rbf.v (definitions/instances byte-identical, theorem
#            statements from the authoritative elaborated types; the proofs
#            need util/sum lemmas absent from the validation-only util/all
#            closure), statement probe, Lean build, export, Rocq import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_model_task_arrival_curve_as_rbf.sh [prepare|check|all]
# Publication is a separate step: publish_model_task_arrival_curve_as_rbf.py.
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/model_task_arrival_curve_as_rbf_final"
typeset curves="$PWD/Validation/.work/experiments/model_task_arrival_curves_final"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/model_task_arrival_curve_as_rbf"
typeset pipe="Validation/planning/v06_pipeline"
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
  [[ ! -e "$work" ]] || { print "CAR_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/model/task/arrival/curve_as_rbf.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="model/task/arrival/curve_as_rbf.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  [[ "$(sha "$curves/olean/Prosa/Model/Task/Arrival/Curves.olean")" == \
    "$(jq -r '.production_olean_sha256' $pipe/model_task_arrival_curves_module_manifest.json)" ]]
  [[ "$(sha "$curves/source/model/task/arrival/curves.vo")" == \
    "$(jq -r '.source_vo_sha256' $pipe/model_task_arrival_curves_module_manifest.json)" ]]
  mkdir -p "$work"/{olean/Validation/fixtures/translation_order,imported,certificates}
  : > "$timing"
  typeset t0=$SECONDS

  cp -R "$curves/source" "$work/source"
  cp "$source_root/model/task/arrival/request_bound_functions.v" "$work/source/model/task/arrival/"
  typeset inv=Validation/planning/v06_dependency/declaration_inventory.csv
  python3 Validation/scripts/extract_v06_semantic_source.py \
    --source-root "$source_root" --source-file model/task/arrival/curve_as_rbf.v \
    --module CurveAsRbfSemanticSource \
    --declarations "$(grep -F 'model/task/arrival/curve_as_rbf.v' $inv | cut -d, -f2 | paste -sd, -)" \
    --computational task_max_rbf,task_min_rbf,MaxArrivalsRBF,MinArrivalsRBF \
    --elaborated-evidence Validation/planning/v06_dependency/declaration_type_evidence.json \
    --qualified-prefix prosa.model.task.arrival.curve_as_rbf \
    --omit-theorem-context-when-elaborated \
    --output "$work/source/CurveAsRbfSemanticSource.v" --metadata "$work/source_extraction.json" \
    > "$work/source_extraction.log"
  cp "$project/$fixtures/CurveAsRbfStatementProbe.v" "$work/source/"
  ( cd "$work/source"; ulimit -s 65520
    opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
      model/task/arrival/request_bound_functions.v ) > "$work/source_build.log" 2>&1
  [[ "$(sha "$work/source/model/task/arrival/request_bound_functions.vo")" == \
    "$(jq -r '.source_vo_sha256' $pipe/model_task_arrival_rbf_module_manifest.json)" ]]
  ( cd "$work/source"; ulimit -s 65520
    for f in CurveAsRbfSemanticSource.v CurveAsRbfStatementProbe.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_type_fingerprint.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  cp -R "$curves/olean/Prosa" "$work/olean/Prosa"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Model/Task/Arrival/RequestBoundFunctions.olean" \
    Prosa/Model/Task/Arrival/RequestBoundFunctions.lean > "$work/rbf_lean_build.log" 2>&1
  [[ "$(sha "$work/olean/Prosa/Model/Task/Arrival/RequestBoundFunctions.olean")" == \
    "$(jq -r '.production_olean_sha256' $pipe/model_task_arrival_rbf_module_manifest.json)" ]]
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Model/Task/Arrival/CurveAsRbf.olean" \
    Prosa/Model/Task/Arrival/CurveAsRbf.lean > "$work/lean_build.log" 2>&1
  for module in Bigcat ArrivalSequence Arrivals CurveAsRbf; do
    lean -DautoImplicit=false -R "$PWD" \
      -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
      "$fixtures/${module}ComputationInterface.lean" > "$work/${module}_interface_build.log" 2>&1
  done
  lean -DautoImplicit=false -R "$PWD" "$fixtures/CurveAsRbfLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/model_task_arrival_curve_as_rbf_export_config.json \
    --output "$work/imported/CurveAsRbf.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  cp "$project/$certs/ImportedCurveAsRbf.v" "$work/imported/"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedCurveAsRbf; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "CAR_PREPARE_PASS: $(wc -l < "$work/imported/CurveAsRbf.out") export lines, $(wc -c < "$work/imported/CurveAsRbf.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedCurveAsRbf.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "CAR_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  cp "$project/$certs"/*.v certificates/
  for m in ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence \
      ArrivalsCorrespondence CurvesCorrespondence RbfCorrespondence \
      CurveAsRbfCorrespondence CurveAsRbfAssumptionAudit; do
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "CAR_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  rocq_c "$project/$fixtures/CurveAsRbfImportedTypeAudit.v" > imported_type_audit.log 2>&1 \
    || { print "CAR_CHECK_FAILED: imported type audit" >&2; tail -30 imported_type_audit.log >&2; exit 1; }
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/curve_as_rbf_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log \
    || { print "CAR_CHECK_FAILED: Lean axiom audit" >&2; tail -30 lean_axiom_classifier.log >&2; exit 1; }
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/curve_as_rbf_assumption_config.json" \
    --log certificates/CurveAsRbfAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log \
    || { print "CAR_CHECK_FAILED: assumption audit" >&2; grep -A4 unexpected assumption_classifier.log | head -30 >&2; exit 1; }
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "CAR_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
