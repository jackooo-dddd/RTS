# Revision: `test/tool/coq-ast-audit.test.ts`

**File**: [`test/tool/coq-ast-audit.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/tool/coq-ast-audit.test.ts) (5 tests; 22 lines with Rocq content; 0 references to a live Rocq run).
**Tests**: Rocq AST audit. **Decision**: Drop and replace.

**Change**: Delete with `coq-ast-audit.ts` (gap-revisions §4). New `tool/lean-gate.test.ts`: (a) benchmark mode maps each `check.py` FAIL reason to its code (frozen change, forbidden token, build failure, statement mismatch, extra axiom); (b) submission stage rejects edits outside the region and accepts added package imports (K1); (c) a solution using `native_decide` is rejected by the axiom check.
