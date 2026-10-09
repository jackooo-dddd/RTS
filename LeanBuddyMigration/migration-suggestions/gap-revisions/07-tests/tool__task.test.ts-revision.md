# Revision: `test/tool/task.test.ts`

**File**: [`test/tool/task.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/tool/task.test.ts) (13 tests; 51 lines with Rocq content; 6 references to a live Rocq run).
**Tests**: task tool: lemma dispatch, submission audit loop. **Decision**: Port.

**Change**: Rocq fixtures → Lean; the submission-audit tests use `LeanGate` stage `submission` and the `<region-check-rejection>` tag (gap-revisions §4 task.ts); the 6 live tests → integration.
