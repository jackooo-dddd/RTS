# Revision: `test/tool/coq-session.test.ts`

**File**: [`test/tool/coq-session.test.ts`](../../../prosabuddy-rocq/packages/opencode/test/tool/coq-session.test.ts) (11 tests; 67 lines with Rocq content; 1 references to a live Rocq run).
**Tests**: interactive session: open at region/error, step, desync, entry-goal kernel check. **Decision**: Rewrite.

**Change**: → `tool/lean-session.test.ts` against Pantograph (integration, needs the pinned Pantograph + project build): open the goal state of a region from the staged file; tactic run changes the state; return to an earlier handle; handles invalid after a source change (BACKEND_DECISION rule 3); entry-goal check accepts a definitionally equal expected goal and rejects a different one (`isDefEq`, coq-session note §6); backend failure is a tool error, not a semantic mismatch.
