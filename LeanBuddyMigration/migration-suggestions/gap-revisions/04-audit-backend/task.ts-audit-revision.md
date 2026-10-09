# Revision: `tool/task.ts` — lemma-submission audit and repair loop only

**File**: [`tool/task.ts`](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts). Only the audit part; the rest is covered by
`tools-advices/02-adapted-tools/task-revision.md`. **Change size**: Modify, Small. **Follows**: DECISIONS D4.

- **Location**: repair prompt [#L402-L412](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L402); submission loop [#L1075-L1110](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L1075); final-audit reporting [#L1138-L1200](../../../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L1138).
- **Current behavior**: after each lemma-helper turn, the staged source is audited at stage `submission`; on
  rejection the helper gets `<ast-audit-rejection>` ("not accepted by the structural Rocq AST audit") and up to
  `maxSubmissionRepairs()` (default 2) more turns.
- **Change**: `CoqAstAudit` → `LeanGate` with stage `submission` (region checks only: outside-edit, forbidden tokens,
  region elaborates). Tag `<ast-audit-rejection>` → `<region-check-rejection>`; text "not accepted by the region check".
  Keep the repair loop and its limit. A rejection here is a normal proof-repair turn, not a controller stop, so it
  is not affected by DECISIONS D5.
