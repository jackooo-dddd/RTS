#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset work="$PWD/Validation/.work/experiments/model_schedule_work_conserving"
typeset package_path=
for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
  package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
done
export LEAN_PATH="$work/olean$package_path"
export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
mkdir -p "$work/olean/Prosa/Model/Schedule" \
  "$work/olean/Validation/fixtures/translation_order"

lean -DautoImplicit=false -R "$PWD" \
  -o "$work/olean/Prosa/Model/Schedule/WorkConserving.olean" \
  Prosa/Model/Schedule/WorkConserving.lean > "$work/lean_build.log" 2>&1
lean -DautoImplicit=false -R "$PWD" \
  Validation/fixtures/translation_order/WorkConservingLeanTypeAudit.lean \
  > "$work/lean_audit.log" 2>&1
for module in Schedule Service Bigcat Ready WorkConserving; do
  lean -DautoImplicit=false -R "$PWD" \
    -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
    "Validation/fixtures/translation_order/${module}ComputationInterface.lean" \
    > "$work/${module}_interface_build.log" 2>&1
done

bash Validation/scripts/export_actual_artifact.sh \
  --config Validation/tooling/model_schedule_work_conserving_export_config.json \
  --output "$work/imported/WorkConserving.out" \
  --log "$work/imported/export.log" \
  --metadata "$work/export_metadata.json"
