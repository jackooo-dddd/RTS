#!/usr/bin/env bash
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
plugin_dir="$script_dir/prosabuddy_elaboration_dump_plugin"
source_file="$plugin_dir/prosabuddy_elaboration_dump.ml"
object_file="$plugin_dir/prosabuddy_elaboration_dump.cmx"
plugin_file="$plugin_dir/prosabuddy_elaboration_dump.cmxs"

ocamlfind ocamlopt \
  -thread \
  -package coq-lsp.fleche,coq-lsp.coq,coq-lsp.serlib,yojson \
  -c \
  -o "$object_file" \
  "$source_file"

ocamlfind ocamlopt \
  -shared \
  -o "$plugin_file" \
  "$object_file"

echo "$plugin_file"
