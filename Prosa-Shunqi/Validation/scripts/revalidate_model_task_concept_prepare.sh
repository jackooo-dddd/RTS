#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset work="$PWD/Validation/.work/experiments/model_task_concept"
typeset predecessor="$PWD/Validation/.work/experiments/model_schedule_work_conserving"
typeset source_predecessor="$PWD/Validation/.work/experiments/model_readiness_basic/source"
typeset source_root
source_root="$(bash Validation/scripts/ensure_pinned_v06_source.sh)"
[[ "$(shasum -a 256 "$source_root/model/task/concept.v" | awk '{print $1}')" == \
  7a1e962028340a19dcfdc9ea39da27d21067551ec40569486f8748e6d554e49b ]]
[[ "$(shasum -a 256 Prosa/Model/Task/Concept.lean | awk '{print $1}')" == \
  3c94ed825564b48eb6b46f0fb78a113a5489d9633dbd3feddfebbe31b588e2dc ]]
for module in Behavior Util; do
  typeset manifest="Validation/planning/v06_pipeline/${(L)module}_all_module_manifest.json"
  typeset expected="$(jq -r '.production_olean_sha256' "$manifest")"
  [[ "$(shasum -a 256 "$predecessor/olean/Prosa/$module/All.olean" | awk '{print $1}')" == "$expected" ]]
done
[[ -s "$predecessor/olean/Prosa/Behavior/All.olean" ]]
[[ -s "$predecessor/olean/Prosa/Util/All.olean" ]]
[[ -s "$source_predecessor/behavior/all.vo" ]]
[[ -s "$source_predecessor/util/all.vo" ]]
mkdir -p "$work" "$work/olean/Prosa/Model/Task" \
  "$work/olean/Validation/fixtures/translation_order" "$work/imported" \
  "$work/certificates"
if [[ ! -e "$work/source" ]]; then
  cp -R "$source_predecessor" "$work/source"
  mkdir -p "$work/source/model/task"
  cp "$source_root/model/task/concept.v" "$work/source/model/task/concept.v"
fi
[[ "$(shasum -a 256 "$work/source/model/task/concept.v" | awk '{print $1}')" == \
  7a1e962028340a19dcfdc9ea39da27d21067551ec40569486f8748e6d554e49b ]]
(
  cd "$work/source"
  opam exec --switch=rocq93rc1 -- rocq c -R "$work/source" prosa \
    model/task/concept.v > "$work/source_build.log" 2>&1
)
cp -R "$predecessor/olean/Prosa/." "$work/olean/Prosa/"
for module in Behavior Util; do
  typeset manifest="Validation/planning/v06_pipeline/${(L)module}_all_module_manifest.json"
  [[ "$(shasum -a 256 "$work/olean/Prosa/$module/All.olean" | awk '{print $1}')" == \
    "$(jq -r '.production_olean_sha256' "$manifest")" ]]
done

typeset package_path=
for package in mathlib plausible proofwidgets batteries aesop importGraph LeanSearchClient Qq Cli; do
  package_path+=":$PWD/.lake/packages/$package/.lake/build/lib/lean"
done
export LEAN_PATH="$work/olean:$predecessor/olean$package_path"
export ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1
lean -DautoImplicit=false -R "$PWD" \
  -o "$work/olean/Prosa/Model/Task/Concept.olean" \
  Prosa/Model/Task/Concept.lean > "$work/lean_build.log" 2>&1
lean -DautoImplicit=false -R "$PWD" \
  Validation/fixtures/translation_order/TaskConceptLeanTypeAudit.lean \
  > "$work/lean_type_audit.log" 2>&1
for module in Bigcat ArrivalSequence TaskConcept; do
  lean -DautoImplicit=false -R "$PWD" \
    -o "$work/olean/Validation/fixtures/translation_order/${module}ComputationInterface.olean" \
    "Validation/fixtures/translation_order/${module}ComputationInterface.lean" \
    > "$work/${module}_interface_build.log" 2>&1
done
bash Validation/scripts/export_actual_artifact.sh \
  --config Validation/tooling/model_task_concept_export_config.json \
  --output "$work/imported/TaskConcept.out" \
  --log "$work/export.log" \
  --metadata "$work/export_metadata.json"
print "CONCEPT_PREPARE_PASS: $(wc -l < "$work/imported/TaskConcept.out") export lines"
