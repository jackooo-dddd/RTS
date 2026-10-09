# Files deleted with the Rocq audit pipeline

Not ported (DECISIONS D4, D6). All in [`scripts/`](../../../prosabuddy-rocq/scripts):

| File | Role in the Rocq version | Why it goes |
|---|---|---|
| `classify_vernac_ast.ml` (262 lines) | OCaml classifier of coq-lsp `astdump` output | no AST pipeline in D4 |
| `build_classify_vernac_ast.sh` | builds the classifier | same |
| `validate_classified_ast.py` (1,021 lines) | the rules | replaced by the gate, see [validate_classified_ast.py-revision.md](validate_classified_ast.py-revision.md) |
| `test_validate_classified_ast.py` (321 lines) | its unit tests | tests the deleted validator; gate tests in gap-revisions §7 |
| `generate_ast_validator_examples.py`, `run_ast_validator_examples.py`, `AST_VALIDATOR.md` | validator examples and docs | same |
| `prosabuddy_elaboration_dump_plugin/`, `build_elaboration_dump_plugin.sh`, `extract_elaboration.py` (212 lines) | Rocq elaboration-dump plugin | not referenced by the app (0 references in `packages/opencode/src`); unused in the replication |
