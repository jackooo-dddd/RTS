#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset work="$PWD/Validation/.work/experiments/model_readiness_basic"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
[[ -s "$work/imported/ImportedReadinessBasicProjection.vo" ]]
[[ -s "$work/source/model/readiness/basic.vo" ]]
cp Validation/certificates/model_readiness_basic/ReadinessBasicInterfaceCertificate.v \
  "$work/certificates/"
cd "$work"
ulimit -s 65520
opam exec --switch=rocq93rc1 -- rocq c \
  -R "$work/source" prosa \
  -Q "$importer" LeanImport -I "$importer" \
  -Q "$work/imported" FoundationImported \
  -Q "$work/certificates" FoundationCertificates \
  certificates/ReadinessBasicInterfaceCertificate.v \
  > certificates/ReadinessBasicInterfaceCertificate.log 2>&1
python3 "$project/Validation/scripts/audit_assumptions.py" \
  --config "$project/Validation/certificates/model_readiness_basic/readiness_basic_assumption_config.json" \
  --log "$work/certificates/ReadinessBasicInterfaceCertificate.log" \
  --output "$work/readiness_basic_interface_assumption_summary.json"

if [[ ${BASIC_COMPILE_SERVICE_DAG:-0} == 1 ]]; then
  [[ -s "$work/imported/ImportedSubadditivity.vo" ]]
  for module in PropSPropFoundation LogicalRelation \
      SubadditivityNatCorrespondence BasicBaseAdapter \
      BasicNatBoolOperations BasicIntervalOperations \
      BasicScheduleOperations BasicJobOperations BasicCorrespondence; do
    opam exec --switch=rocq93rc1 -- rocq c \
      -R "$work/source" prosa \
      -Q "$importer" LeanImport -I "$importer" \
      -Q "$work/imported" FoundationImported \
      -Q "$work/certificates" FoundationCertificates \
      "certificates/$module.v" > "certificates/$module.log" 2>&1
    print "compiled $module"
  done
fi
