#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset work="$PWD/Validation/.work/experiments/model_task_concept"
typeset predecessor="$PWD/Validation/.work/experiments/model_schedule_work_conserving"
[[ "$(shasum -a 256 "$work/olean/Prosa/Model/Task/Concept.olean" | awk '{print $1}')" == \
  c6b150ba6d78e705cb143e10dd9c054265d651fc18f1eba051f45435bf39d31c ]]
typeset package_path=
for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
  package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
done
export LEAN_PATH="$work/olean:$predecessor/olean$package_path"
export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
lean -DautoImplicit=false -R "$PWD" \
  Validation/fixtures/translation_order/TaskConceptLeanTypeAudit.lean \
  > "$work/lean_type_audit.log" 2>&1
