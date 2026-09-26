#!/bin/zsh
# Fresh prepare/check for model/priority/definitions.v (Rank 72).
#   prepare: source acquisition, Lean build, Lean audit, export, Rocq import
#   check:   certificate DAG, type audits, fail-closed assumption audit
# Usage: validate_model_priority_definitions.sh [prepare|check|all]
# Publication is a separate step: publish_model_priority_definitions.py.
#
# Source binding: the pinned util/list.v does not compile under Rocq 9.3
# (proof stack overflow).  priority/definitions.v uses none of its constants,
# only its re-exports (zify, util.supremum).  util/list.v is therefore replaced
# by the proof-free semantic extraction of extract_v06_semantic_source.py
# (computational bodies byte-identical, lemma statements as Prop definitions,
# identical Require/Export lines, no axiom/Admitted), and the 20 elaborated
# types are re-fingerprinted against declaration_type_evidence.json.
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset stage="${1:-all}"
typeset work="$PWD/Validation/.work/experiments/model_priority_definitions_final"
typeset concept="$PWD/Validation/.work/experiments/model_task_concept"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset fixtures="Validation/fixtures/translation_order"
typeset certs="Validation/certificates/model_priority_definitions"
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
    -Q "$work/pcertificates" PriorityCertificates "$@"
}

prepare() {
  [[ ! -e "$work" ]] || { print "PRIORITY_PREPARE_REFUSED: $work exists" >&2; exit 1; }
  [[ "$(sha "$source_root/model/priority/definitions.v")" == \
    "$(python3 -c 'import csv,sys; print(next(r["sha256"] for r in csv.DictReader(open(sys.argv[1])) if r["file"]=="model/priority/definitions.v"))' \
      Validation/planning/v06_dependency/file_inventory.csv)" ]]
  [[ "$(sha "$concept/olean/Prosa/Model/Task/Concept.olean")" == \
    "$(jq -r '.production_olean_sha256' Validation/planning/v06_pipeline/model_task_concept_module_manifest.json)" ]]
  [[ "$(sha "$concept/source/model/task/concept.vo")" == \
    "$(jq -r '.artifact_hashes.source_vo_sha256' Validation/planning/v06_pipeline/model_task_concept_module_manifest.json)" ]]
  mkdir -p "$work"/{olean/Prosa/Model/Priority,imported,certificates,pcertificates}
  : > "$timing"
  typeset t0=$SECONDS

  cp -R "$concept/source" "$work/source"
  mkdir -p "$work/source/model/priority"
  cp "$source_root/util/rel.v" "$source_root/util/supremum.v" "$source_root/util/tactics.v" "$work/source/util/"
  cp "$source_root/model/priority/definitions.v" "$work/source/model/priority/definitions.v"
  ( cd "$work/source" && patch -s -p1 -i "$project/Validation/patches/prosa-v06-rocq93-util-tactics.patch" )
  typeset inv=Validation/planning/v06_dependency/declaration_inventory.csv
  python3 Validation/scripts/extract_v06_semantic_source.py \
    --source-root "$source_root" --source-file util/list.v --module ListSemanticSource \
    --declarations "$(grep -F 'util/list.v' $inv | cut -d, -f2 | paste -sd, -)" \
    --computational "$(grep -F 'util/list.v' $inv | awk -F, '$4=="Definition"||$4=="Fixpoint"{print $2}' | paste -sd, -)" \
    --elaborated-evidence Validation/planning/v06_dependency/declaration_type_evidence.json \
    --qualified-prefix prosa.util.list \
    --output "$work/source/util/list.v" --metadata "$work/list_extraction.json" > "$work/list_extraction.log"
  ( cd "$work/source"; ulimit -s 65520
    for f in util/tactics.v util/rel.v util/supremum.v util/list.v model/priority/definitions.v; do
      opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa "$f"
    done ) > "$work/source_build.log" 2>&1
  opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
    "$project/$fixtures/PriorityDefinitionsTypeFingerprintProbe.v" > "$work/source_type_fingerprint.log" 2>&1
  opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
    "$project/$fixtures/PriorityDefinitionsSourceAssumptionAudit.v" > "$work/source_assumption_audit.log" 2>&1
  stamp source_acquisition FRESH $((SECONDS - t0)); t0=$SECONDS

  cp -R "$concept/olean/Prosa/." "$work/olean/Prosa/"
  typeset package_path=
  for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
    package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
  done
  export LEAN_PATH="$work/olean$package_path"
  export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
  lean -DautoImplicit=false -R "$PWD" -o "$work/olean/Prosa/Model/Priority/Definitions.olean" \
    Prosa/Model/Priority/Definitions.lean > "$work/lean_build.log" 2>&1
  lean -DautoImplicit=false -R "$PWD" "$fixtures/PriorityDefinitionsLeanTypeAudit.lean" \
    > "$work/lean_type_audit.log" 2>&1
  stamp lean_build FRESH $((SECONDS - t0)); t0=$SECONDS

  bash Validation/scripts/export_actual_artifact.sh \
    --config Validation/tooling/model_priority_definitions_export_config.json \
    --output "$work/imported/PriorityDefinitions.out" \
    --log "$work/export.log" --metadata "$work/export_metadata.json"
  stamp export FRESH $((SECONDS - t0)); t0=$SECONDS

  cp Validation/imported/foundation_slice_2/Subadditivity.out \
    Validation/imported/foundation_slice_2/ImportedSubadditivity.v "$work/imported/"
  cp "$project/$certs/ImportedPriorityDefinitions.v" "$work/imported/"
  ( cd "$work/imported"; ulimit -s 65520
    for m in ImportedSubadditivity ImportedPriorityDefinitions; do
      opam exec --switch=rocq93rc1 -- rocq c -Q "$importer" LeanImport -I "$importer" \
        -Q "$work/imported" FoundationImported "$m.v"
    done ) > "$work/import.log" 2>&1
  stamp rocq_import FRESH $((SECONDS - t0))
  print "PRIORITY_PREPARE_PASS: $(wc -l < "$work/imported/PriorityDefinitions.out") export lines, $(wc -c < "$work/imported/PriorityDefinitions.out") bytes"
}

check() {
  [[ -s "$work/imported/ImportedPriorityDefinitions.vo" ]]
  typeset t0=$SECONDS
  cd "$work"; ulimit -s 65520
  mkdir -p certificates pcertificates
  for m in PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence; do
    cp "$project/Validation/certificates/common/$m.v" certificates/
    rocq_c "certificates/$m.v" > "certificates/$m.log" 2>&1 \
      || { print "PRIORITY_CHECK_FAILED: $m" >&2; tail -30 "certificates/$m.log" >&2; exit 1; }
  done
  cp "$project/$certs"/Priority*.v pcertificates/
  for m in PriorityBaseAdapter PriorityListAdapter PriorityStaticOrder PriorityDynamicOrder \
      PriorityPolicyProperties PriorityDerived PriorityAntisymmetric \
      PriorityDefinitionsTypeAudit PriorityAssumptionAudit; do
    rocq_c "pcertificates/$m.v" > "pcertificates/$m.log" 2>&1 \
      || { print "PRIORITY_CHECK_FAILED: $m" >&2; tail -30 "pcertificates/$m.log" >&2; exit 1; }
  done
  stamp certificate_compile FRESH $((SECONDS - t0)); t0=$SECONDS
  python3 "$project/Validation/scripts/audit_lean_axioms.py" \
    --config "$project/$certs/priority_lean_axiom_config.json" \
    --log lean_type_audit.log --output lean_axiom_summary.json > lean_axiom_classifier.log
  python3 "$project/Validation/scripts/audit_assumptions.py" \
    --config "$project/$certs/priority_assumption_config.json" \
    --log pcertificates/PriorityAssumptionAudit.log --output assumption_summary.json \
    > assumption_classifier.log
  stamp assumption_audit FRESH $((SECONDS - t0))
  print "PRIORITY_CHECK_PASS"
}

case "$stage" in
  prepare) prepare ;;
  check) check ;;
  all) prepare; check ;;
  *) print "unknown stage: $stage" >&2; exit 2 ;;
esac
