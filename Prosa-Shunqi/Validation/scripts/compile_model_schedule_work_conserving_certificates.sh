#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset work="$PWD/Validation/.work/experiments/model_schedule_work_conserving"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
cp Validation/certificates/common/PropSPropFoundation.v \
  Validation/certificates/common/LogicalRelation.v \
  Validation/certificates/common/SubadditivityNatCorrespondence.v \
  "$work/certificates/"
cd "$work"
ulimit -s 65520
for module in PropSPropFoundation LogicalRelation \
    SubadditivityNatCorrespondence ReadyBaseAdapter ReadyNatBoolOperations \
    ReadyIntervalOperations ReadyScheduleOperations ReadyJobOperations \
    ReadyServiceCorrespondence ReadyArrivalBaseAdapter ReadyArrivalOperations \
    ReadyArrivalCorrespondence ReadyCorrespondence WorkConservingCorrespondence \
    WorkConservingExactTypeGuards WorkConservingAssumptionAudit; do
  opam exec --switch=rocq93rc1 -- rocq c \
    -R "$work/source" prosa \
    -Q "$importer" LeanImport -I "$importer" \
    -Q "$work/imported" FoundationImported \
    -Q "$work/certificates" FoundationCertificates \
    "certificates/$module.v" > "certificates/$module.log" 2>&1
done
python3 "$project/Validation/scripts/audit_assumptions.py" \
  --config "$project/Validation/certificates/model_schedule_work_conserving/work_conserving_assumption_config.json" \
  --log "$work/certificates/WorkConservingAssumptionAudit.log" \
  --output "$work/certificates/assumption_summary.json"
