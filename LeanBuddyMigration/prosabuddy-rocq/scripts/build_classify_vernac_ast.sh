#!/usr/bin/env bash
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
output=${1:-"$script_dir/classify_vernac_ast"}

# Link all installed coq-lsp serializers.  astdump encodes tactic/plugin
# arguments through serlib; without the corresponding registration module the
# classifier cannot deserialize VernacExtend records.
serlib_packages=$(
  ocamlfind list 2>/dev/null \
    | awk '$1 ~ /^coq-lsp\.serlib(\.|$)/ {print $1}' \
    | paste -sd, -
)

if [ -z "$serlib_packages" ]; then
  echo "error: no coq-lsp.serlib packages found in the active opam switch" >&2
  exit 1
fi

ocamlfind ocamlopt \
  -thread \
  -linkall \
  -linkpkg \
  -package "$serlib_packages,coq-core.vernac,yojson" \
  -o "$output" \
  "$script_dir/classify_vernac_ast.ml"

echo "$output"
