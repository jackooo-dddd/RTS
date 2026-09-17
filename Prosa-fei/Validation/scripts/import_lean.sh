#!/usr/bin/env bash
set -euo pipefail

here=$(cd "$(dirname "$0")/.." && pwd)
importer_src=${ROCQLI_SRC:?Set ROCQLI_SRC to a built rocq-lean-import source tree}
switch_name=${IMPORT_OPAM_SWITCH:-validation-rocq-9.3}
target=${1:-ImportedScheduled.v}

cd "$here/rocq"
opam exec --switch="$switch_name" -- rocq c \
  -Q "$importer_src/src" LeanImport -I "$importer_src/src" "$target"
