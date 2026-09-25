#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset work="$PWD/Validation/.work/experiments/analysis_definitions_overheads_schedule_change"
typeset predecessor="$PWD/Validation/.work/experiments/model_schedule_work_conserving"
typeset overheads="$PWD/Validation/.work/experiments/model_processor_overheads"
typeset concept="$PWD/Validation/.work/experiments/model_task_concept"
typeset platform="$PWD/Validation/.work/experiments/model_processor_platform_properties"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
typeset source_root
source_root="$(bash Validation/scripts/ensure_pinned_v06_source.sh)"
typeset target_source="analysis/definitions/overheads/schedule_change.v"
typeset target_lean="Prosa/Analysis/Definitions/Overheads/ScheduleChange.lean"
typeset config="Validation/tooling/analysis_definitions_overheads_schedule_change_export_config.json"
typeset mode="${1:-}"
[[ "$mode" == prepare || "$mode" == import || "$mode" == certificates ]]

verify_sha() {
  [[ -s "$1" ]]
  [[ "$(shasum -a 256 "$1" | awk '{print $1}')" == "$2" ]]
}

verify_sha "$source_root/$target_source" \
  bda24718f11d3e3e3874782383cb28c58cb29a786b9466d68fb0c9476a4be199
verify_sha "$overheads/source/model/processor/overheads.vo" \
  "$(jq -r '.artifact_hashes.source_vo' Validation/planning/v06_pipeline/model_processor_overheads_module_manifest.json)"
verify_sha "$overheads/olean/Prosa/Model/Processor/Overheads.olean" \
  "$(jq -r '.artifact_hashes.production_olean' Validation/planning/v06_pipeline/model_processor_overheads_module_manifest.json)"
verify_sha "$predecessor/source/behavior/all.vo" \
  9dce3426eee8d36ce492d52579091ccb409c90d8b5f7ed1b451b13a18b46bf9c
verify_sha "$importer/lean_import.cmxs" \
  c3a10b84f88ff66a3fcff8e15e3c0a6a307592b45726c612fa8a95b061d97982
typeset package_path=
for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
  package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
done
export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1

if [[ "$mode" == prepare ]]; then
  [[ ! -e "$work/source" && ! -e "$work/olean" ]]
  mkdir -p "$work" "$work/portable/imported" "$work/portable/certificates"
  cp -R "$predecessor/source" "$work/source"
  mkdir -p "$work/source/model/processor" "$work/source/analysis/definitions/overheads"
  cp "$overheads/source/model/processor/overheads.v" "$work/source/model/processor/"
  cp "$overheads/source/model/processor/overheads.vo" "$work/source/model/processor/"
  cp "$source_root/$target_source" "$work/source/$target_source"
  verify_sha "$work/source/$target_source" \
    bda24718f11d3e3e3874782383cb28c58cb29a786b9466d68fb0c9476a4be199
  (
    cd "$work/source"
    opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
      "$target_source" > "$work/source_compile.log" 2>&1
  )
  cp Validation/fixtures/translation_order/ScheduleChangeSourceTypeAudit.v \
    "$work/source/ScheduleChangeSourceTypeAudit.v"
  (
    cd "$work/source"
    opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
      ScheduleChangeSourceTypeAudit.v > "$work/source_type_audit.log" 2>&1
  )
  cp -R "$predecessor/olean" "$work/olean"
  mkdir -p "$work/olean/Prosa/Model/Processor" \
    "$work/olean/Prosa/Analysis/Definitions/Overheads" \
    "$work/olean/Validation/fixtures/translation_order"
  cp "$overheads/olean/Prosa/Model/Processor/Overheads.olean" \
    "$work/olean/Prosa/Model/Processor/"
  export LEAN_PATH="$work/olean:$overheads/olean$package_path"
  lean -DautoImplicit=false -R "$PWD" \
    -o "$work/olean/Prosa/Analysis/Definitions/Overheads/ScheduleChange.olean" \
    "$target_lean" > "$work/lean_build.log" 2>&1
  lean -DautoImplicit=false -R "$PWD" \
    Validation/fixtures/translation_order/ScheduleChangeLeanTypeAudit.lean \
    > "$work/lean_type_audit.log" 2>&1
  lean -DautoImplicit=false -R "$PWD" \
    -o "$work/olean/Validation/fixtures/translation_order/ScheduleChangeComputationInterface.olean" \
    Validation/fixtures/translation_order/ScheduleChangeComputationInterface.lean \
    > "$work/interface_build.log" 2>&1
  bash Validation/scripts/export_actual_artifact.sh \
    --config "$config" \
    --output "$work/portable/imported/ScheduleChangeFull.out" \
    --log "$work/export.log" \
    --metadata "$work/export_metadata.json"
  print "SCHEDULE_CHANGE_PREPARE_PASS: $(wc -l < "$work/portable/imported/ScheduleChangeFull.out") lines"
  exit 0
fi

verify_sha "$work/portable/imported/ScheduleChangeFull.out" \
  "$(jq -r '.output_sha256' "$work/export_metadata.json")"
verify_sha "$work/olean/Prosa/Analysis/Definitions/Overheads/ScheduleChange.olean" \
  "$(shasum -a 256 "$work/olean/Prosa/Analysis/Definitions/Overheads/ScheduleChange.olean" | awk '{print $1}')"

if [[ "$mode" == import ]]; then
  cp Validation/certificates/analysis_definitions_overheads_schedule_change/ImportedScheduleChange.v \
    "$work/portable/imported/"
  cd "$work/portable/imported"
  ulimit -s 65520
  opam exec --switch=rocq93rc1 -- rocq c \
    -Q "$importer" LeanImport -I "$importer" \
    -Q "$work/portable/imported" FoundationImported \
    ImportedScheduleChange.v > "$work/import.log" 2>&1
  print "SCHEDULE_CHANGE_IMPORT_PASS: $(shasum -a 256 ImportedScheduleChange.vo | awk '{print $1}')"
  exit 0
fi

[[ "$mode" == certificates ]]
[[ -s "$work/portable/imported/ImportedScheduleChange.vo" ]]
for module in LogicalRelation PropSPropFoundation SubadditivityNatCorrespondence; do
  cp "$concept/certificates/$module.vo" "$work/portable/certificates/"
done
cp "$platform/imported/ImportedSubadditivity.vo" "$work/portable/imported/"
for module in ScheduleChangeBaseAdapter ScheduleChangeStateAdapter \
    ScheduleChangeOptionOperations ScheduleChangeIntervalOperations \
    ScheduleChangeListOperations ScheduleChangeCorrespondence \
    ScheduleChangeExactTypeGuards ScheduleChangeAssumptionAudit; do
  cp "Validation/certificates/analysis_definitions_overheads_schedule_change/$module.v" \
    "$work/portable/certificates/"
done
cd "$work"
ulimit -s 65520
for module in ScheduleChangeBaseAdapter ScheduleChangeStateAdapter \
    ScheduleChangeOptionOperations ScheduleChangeIntervalOperations \
    ScheduleChangeListOperations ScheduleChangeCorrespondence \
    ScheduleChangeExactTypeGuards ScheduleChangeAssumptionAudit; do
  opam exec --switch=rocq93rc1 -- rocq c \
    -R "$work/source" prosa \
    -Q "$importer" LeanImport -I "$importer" \
    -Q "$work/portable/imported" FoundationImported \
    -Q "$work/portable/certificates" FoundationCertificates \
    "portable/certificates/$module.v" > "$work/$module.log" 2>&1
  print "compiled $module"
done
python3 "$project/Validation/scripts/audit_assumptions.py" \
  --config "$project/Validation/certificates/analysis_definitions_overheads_schedule_change/schedule_change_assumption_config.json" \
  --log "$work/ScheduleChangeAssumptionAudit.log" \
  --output "$work/assumption_summary.json" > "$work/assumption_audit_stdout.log"
print 'SCHEDULE_CHANGE_CERTIFICATES_PASS'
