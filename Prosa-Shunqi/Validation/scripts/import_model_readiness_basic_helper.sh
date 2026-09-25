#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset work="$PWD/Validation/.work/experiments/model_readiness_basic"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
[[ -s "$work/imported/ReadinessBasicProjection.out" ]]
[[ -s "$work/export_metadata.json" ]]
[[ -d "$work/source" ]]
[[ -d "$importer" ]]
cd "$work/imported"
ulimit -s 65520
opam exec --switch=rocq93rc1 -- rocq c \
  -R "$work/source" prosa \
  -Q "$importer" LeanImport -I "$importer" \
  -Q "$work/imported" FoundationImported \
  ImportedReadinessBasicProjection.v \
  > ImportedReadinessBasicProjection.log 2>&1
