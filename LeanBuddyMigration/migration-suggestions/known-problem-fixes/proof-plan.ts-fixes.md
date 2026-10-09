# Fixes: `tool/proof-plan.ts`

**File**: [`tool/proof-plan.ts`](../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts). **Implements**: DECISIONS D9 (K2), D10 (K6, K7).

**K2 — amendment action | Modify, Medium**

- **Location**: tool parameters [#L26-L40](../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L26); convergence/budget logic and `recommended_action` [#L1130-L1165](../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L1130).
- **Change**: add `action: "amend"` with `amendment: { node, depends_on, inserts_before: <admit_id>, addresses_escalation: <task_id> }`. Allowed only when the plan is locked and a region is `awaiting_amendment` (proof-workflow fixes). Review the new node like any plan node (contract fields, dependency closure, statement elaborates in context via the equivalence service); on acceptance update the locked plan in place and return the region text to materialise. Rejections return reasons and do not count (D9). Amendments do not use the semantic-revision budget (`MAX_SEMANTIC_PLAN_REVISIONS`), which stays for pre-acceptance planning.

**K6 — root goal by elaboration | Modify, Small**

- **Location**: `normalizeGoal` [#L163](../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L163); `bound_root_goal_mismatch` check [#L875-L886](../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L875).
- **Change**: compare the submitted `root_goal` with the bound theorem's statement through the equivalence service (definitional equality in the theorem's context). Keep `normalizeGoal` only as a cheap first pass (if the normalised texts are equal, skip the Lean call). A mismatch that the service reports as equivalent is accepted; a real mismatch is rejected **without** spending a semantic revision when the rest of the plan is unchanged (it is a binding error, not a new plan).

**K7 — prose `normal_form` rejected at plan time | Modify, Small**

- **Location**: `reviewProofPlan` [#L493](../../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L493).
- **Change**: every delegated node's `normal_form` must elaborate as a Lean `Prop` in the theorem context (equivalence service, "elaborates" check). English prose or a truncated expression is a plan-review error with a repair hint, so it can never become the locked reference for later checkpoints (S22).
