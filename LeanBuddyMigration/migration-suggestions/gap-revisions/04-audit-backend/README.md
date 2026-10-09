# §4 Audit backend — revision set

**Decision**: DECISIONS D4 (semantic gate, the Lean benchmark's `check.py` approach). The Rocq pipeline
(coq-lsp `astdump` → OCaml classifier → 1,021-line Python validator) is not ported.

| File | Change | Revision file |
|---|---|---|
| `packages/opencode/src/tool/coq-ast-audit.ts` | Rewrite as `tool/lean-gate.ts` (same API shape) | [coq-ast-audit.ts-revision.md](coq-ast-audit.ts-revision.md) |
| `scripts/validate_classified_ast.py` | Replaced by the gate rules (no Python validator) | [validate_classified_ast.py-revision.md](validate_classified_ast.py-revision.md) |
| `packages/opencode/src/tool/coqc.ts` (final-gate call) | Call `LeanGate` | [coqc.ts-audit-revision.md](coqc.ts-audit-revision.md) |
| `packages/opencode/src/tool/checkpoint.ts` (final-gate call) | Call `LeanGate` | [checkpoint.ts-audit-revision.md](checkpoint.ts-audit-revision.md) |
| `packages/opencode/src/tool/task.ts` (submission audit + repair prompt) | Call `LeanGate` stage `submission` | [task.ts-audit-revision.md](task.ts-audit-revision.md) |
| 9 files to delete | Delete | [removed-files.md](removed-files.md) |

The tools-advices notes `04-helper-modules/coq-ast-audit-revision.md`, `01-core-tools/coqc-revision.md`,
`01-core-tools/checkpoint-revision.md` and `02-adapted-tools/task-revision.md` cover the rest of those files; where they
say "audit Lean syntax and elaboration information", this revision set replaces that with D4.
