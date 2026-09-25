#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset work="$PWD/Validation/.work/experiments/model_schedule_scheduled"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
cp Validation/certificates/common/PropSPropFoundation.v \
  Validation/certificates/common/LogicalRelation.v \
  Validation/certificates/common/SubadditivityNatCorrespondence.v \
  "$work/certificates/"
for module in ReadyArrivalBaseAdapter ReadyArrivalOperations \
    ReadyArrivalCorrespondence ScheduledStateBaseAdapter \
    ScheduledStateOperations ScheduledCorrespondence \
    ScheduledExactTypeGuards ScheduledAssumptionAudit; do
  cp "$project/Validation/certificates/model_schedule_scheduled/$module.v" \
    "$work/certificates/$module.v"
done
cd "$work"
ulimit -s 65520
for module in PropSPropFoundation LogicalRelation \
    SubadditivityNatCorrespondence ReadyArrivalBaseAdapter \
    ReadyArrivalOperations ReadyArrivalCorrespondence \
    ScheduledStateBaseAdapter ScheduledStateOperations \
    ScheduledCorrespondence ScheduledExactTypeGuards ScheduledAssumptionAudit; do
  opam exec --switch=rocq93rc1 -- rocq c \
    -R "$work/source" prosa \
    -Q "$importer" LeanImport -I "$importer" \
    -Q "$work/imported" FoundationImported \
    -Q "$work/certificates" FoundationCertificates \
    "certificates/$module.v" > "certificates/$module.log" 2>&1
done
python3 "$project/Validation/scripts/audit_assumptions.py" \
  --config "$project/Validation/certificates/model_schedule_scheduled/scheduled_assumption_config.json" \
  --log "$work/certificates/ScheduledAssumptionAudit.log" \
  --output "$work/assumption_summary.json"
