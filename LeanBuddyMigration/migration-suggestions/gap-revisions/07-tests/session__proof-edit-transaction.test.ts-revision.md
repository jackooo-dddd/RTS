# Revision: `test/session/proof-edit-transaction.test.ts`

**File**: [`test/session/proof-edit-transaction.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/session/proof-edit-transaction.test.ts) (25 tests; 77 lines with Rocq content; 5 references to a live Rocq run).
**Tests**: staged proof revisions, recovery, scope. **Decision**: Port.

**Change**: Rewrite the Rocq sources (proof_region markers, `admit.`, `Qed.`) as Lean sources with `:= (by …)` regions and `sorry` (R1). The 5 tests that compile through `coqc` become integration tests calling `lean_check` behind `PROSABUDDY_LEAN_INTEGRATION=1`.
