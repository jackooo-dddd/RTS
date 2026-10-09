# Revision: `test/session/prompt.test.ts`

**File**: [`test/session/prompt.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/session/prompt.test.ts) (18 tests; 44 lines with Rocq content; 6 references to a live Rocq run).
**Tests**: runtime controller: queued messages, accepted-plan tool gate, cache projection, file binding. **Decision**: Port.

**Change**: `.v` fixtures → `Solution.lean`; tool names per D2; finalization text without `Qed.` (gap-revisions §1). Add tests for the structured `controller_stop` record (§1 item 8). Note: 9 tests already time out (5 s) on pristine 8e1de8c in our environment — fix the timeout before porting, it is not a migration signal.
