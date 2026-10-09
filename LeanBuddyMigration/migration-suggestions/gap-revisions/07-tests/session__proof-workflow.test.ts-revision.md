# Revision: `test/session/proof-workflow.test.ts`

**File**: [`test/session/proof-workflow.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/session/proof-workflow.test.ts) (107 tests; 458 lines with Rocq content; 28 references to a live Rocq run).
**Tests**: proof workflow: plan materialisation, region parsing, scheduling, guards, checkpoints. **Decision**: Port in stages.

**Change**: Largest file (6,984 lines). Order: (1) region/contract parsing — Lean fixtures, include the upstream 8e1de8c parser cases (tools-advices proof-workflow note §8: `*` inside values, JSON `depends_on`, `(none)`) and Lean-specific ones (type ascriptions `(x : Job)`, `∑ i ∈ s, …`, `⟨…⟩`); (2) scheduling and guard tests — tool names per D2, passive/active table (§1 item 3); (3) the 28 tests that run `coqc` → integration tests with `lean_check`. When KNOWN_PROBLEMS K2/K5 are implemented, add tests: plan amendment adds a bridge node; plan visible from a child and a fresh session.
