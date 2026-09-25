#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset work="$PWD/Validation/.work/experiments/model_readiness_basic"
typeset package_path=
for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
  package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
done
export LEAN_PATH="$work/olean$package_path"
export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
mkdir -p "$work/olean/Prosa/Model/Readiness" \
  "$work/olean/Validation/fixtures/translation_order" \
  "$work/imported" "$work/certificates"

if [[ ${BASIC_REUSE_COMPILED:-0} == 1 ]]; then
  [[ "$(shasum -a 256 Prosa/Model/Readiness/Basic.lean | awk '{print $1}')" == \
    5a66ed32baf9a0f6fe7588f0d71f27abe22e6cf8a7abbc6d0807385d2f26ca1b ]]
  [[ "$(shasum -a 256 "$work/olean/Prosa/Model/Readiness/Basic.olean" | awk '{print $1}')" == \
    48125a49b59a5e4d7e97d78fe3da30f265511329c667202f5b5a8385e51b34fc ]]
  [[ "$(shasum -a 256 "$work/olean/Prosa/Behavior/All.olean" | awk '{print $1}')" == \
    "$(jq -r '.production_olean_sha256' Validation/planning/v06_pipeline/behavior_all_module_manifest.json)" ]]
  [[ -s "$work/lean_audit.log" ]]
  grep -q "'Prosa.Model.Readiness.Basic.basic_ready_instance' depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$work/lean_audit.log"
  print 'BASIC_TARGET_COMPILE=VERIFIED_CACHE; resuming after completed Lean audit'
else
  lean -DautoImplicit=false -R "$PWD" \
    -o "$work/olean/Prosa/Model/Readiness/Basic.olean" \
    Prosa/Model/Readiness/Basic.lean > "$work/lean_build.log" 2>&1
  lean -DautoImplicit=false -R "$PWD" \
    Validation/fixtures/translation_order/ReadinessBasicLeanInterfaceAudit.lean \
    > "$work/lean_audit.log" 2>&1
fi
for module in Schedule Service ReadinessBasic; do
  lean -DautoImplicit=false -R "$PWD" \
    -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
    "Validation/fixtures/translation_order/${module}ComputationInterface.lean" \
    > "$work/${module}_interface_build.log" 2>&1
done
bash Validation/scripts/export_actual_artifact.sh \
  --config Validation/tooling/model_readiness_basic_projection_export_config.json \
  --output "$work/imported/ReadinessBasicProjection.out" \
  --log "$work/export.log" \
  --metadata "$work/export_metadata.json"
