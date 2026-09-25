#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset work="$PWD/Validation/.work/experiments/model_task_concept"
typeset foundation="$PWD/Validation/.work/experiments/model_processor_platform_properties"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
[[ -s "$work/imported/ImportedTaskConcept.vo" ]]
[[ -s "$work/source/model/task/concept.vo" ]]
typeset -A expected
expected[ImportedSubadditivity.vo]=9d934dfd1a8c9f5773146cf5f9f97e766e7c39ace3d2a7f371fd1b3890b21452
expected[SubadditivityNatCorrespondence.vo]=b0f41061b1ec56adedfc8ab948d1c71e5875a8f8df265539a8610156dd7a49bb
expected[LogicalRelation.vo]=32da499429928712bcefc228d6bc4ad13b383cfbf8a86f95361d0de972cc662f
expected[PropSPropFoundation.vo]=e57cfcda7537a04b25dd3de1b2cae0312ef6ee081b91571db3202cb92f703cf6
for name in ${(k)expected}; do
  if [[ "$name" == ImportedSubadditivity.vo ]]; then
    typeset source="$foundation/imported/$name"
    typeset target="$work/imported/$name"
  else
    typeset source="$foundation/certificates/$name"
    typeset target="$work/certificates/$name"
  fi
  [[ "$(shasum -a 256 "$source" | awk '{print $1}')" == "${expected[$name]}" ]]
  cp "$source" "$target"
  [[ "$(shasum -a 256 "$target" | awk '{print $1}')" == "${expected[$name]}" ]]
done
python3 Validation/certificates/model_task_concept/replay_artifact_adapters.py \
  --source-root "$project" \
  --imported-artifact "$work/imported/ImportedTaskConcept.vo" \
  --output-dir "$work/certificates"
for module in ConceptOperations ConceptClasses ConceptCorrespondence \
    ConceptTypeAudit ConceptAssumptionAudit; do
  cp "Validation/certificates/model_task_concept/$module.v" \
    "$work/certificates/$module.v"
done
cd "$work"
ulimit -s 65520
for module in ReadyArrivalBaseAdapter ConceptOperations \
    ReadyArrivalCorrespondence ConceptClasses ConceptCorrespondence \
    ConceptTypeAudit ConceptAssumptionAudit; do
  opam exec --switch=rocq93rc1 -- rocq c \
    -R "$work/source" prosa \
    -Q "$importer" LeanImport -I "$importer" \
    -Q "$work/imported" FoundationImported \
    -Q "$work/certificates" FoundationCertificates \
    "certificates/$module.v" > "certificates/$module.log" 2>&1
  print "compiled $module"
done
python3 "$project/Validation/scripts/audit_assumptions.py" \
  --config "$project/Validation/certificates/model_task_concept/concept_assumption_config.json" \
  --log "$work/certificates/ConceptAssumptionAudit.log" \
  --output "$work/assumption_summary.json" > "$work/assumption_audit_stdout.log"
print 'CONCEPT_CERTIFICATES_PASS'
