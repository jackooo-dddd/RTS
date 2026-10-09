# Revision: `test/tool/coq-diagnostics.test.ts`

**File**: [`test/tool/coq-diagnostics.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/tool/coq-diagnostics.test.ts) (3 tests; 10 lines with Rocq content; 0 references to a live Rocq run).
**Tests**: compiler error parsing. **Decision**: Port (rename).

**Change**: → `tool/lean-diagnostics.test.ts`: parse Lean's `file:line:col: error: …` format and multi-line messages; keep the summary rules (tools-advices coq-diagnostics note).
