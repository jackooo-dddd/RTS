#!/bin/zsh
set -euo pipefail

cd "${0:A:h:h:h}"
typeset project="$PWD"
typeset work="$PWD/Validation/.work/experiments/model_task_concept"
typeset importer="$PWD/Validation/.work/tooling/rocq-lean-import/src"
[[ -s "$work/imported/TaskConcept.out" ]]
[[ -s "$work/export_metadata.json" ]]
[[ "$(shasum -a 256 "$work/imported/TaskConcept.out" | awk '{print $1}')" == \
  "$(jq -r '.output_sha256' "$work/export_metadata.json")" ]]
[[ "$(shasum -a 256 "$importer/lean_import.cmxs" | awk '{print $1}')" == \
  c3a10b84f88ff66a3fcff8e15e3c0a6a307592b45726c612fa8a95b061d97982 ]]
cp Validation/certificates/model_task_concept/ImportedTaskConcept.v "$work/imported/"
cd "$work/imported"
ulimit -s 65520
opam exec --switch=rocq93rc1 -- rocq c \
  -Q "$importer" LeanImport -I "$importer" \
  -Q "$work/imported" FoundationImported \
  ImportedTaskConcept.v > "$work/import.log" 2>&1
print "CONCEPT_IMPORT_PASS: $(shasum -a 256 ImportedTaskConcept.vo | awk '{print $1}')"
