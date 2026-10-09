# Revision: `test/tool/proof-review.test.ts`

**File**: [`test/tool/proof-review.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/tool/proof-review.test.ts) (39 tests; 98 lines with Rocq content; 0 references to a live Rocq run).
**Tests**: `proof_plan` semantic review. **Decision**: Port.

**Change**: Lean statements in plans. Add the KNOWN_PROBLEMS K6 test: a root goal that differs from the theorem only in spacing/notation (`→` vs `->`, `∀` vs `forall`, `(a, b)` vs `(a,b)`) must be accepted and must not spend a planning revision.
