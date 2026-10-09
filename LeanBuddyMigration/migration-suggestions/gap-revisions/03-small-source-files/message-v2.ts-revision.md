# Revision: `session/message-v2.ts` (tool-output cache projection)

**File**: [`session/message-v2.ts`](../../../prosabuddy-rocq/packages/opencode/src/session/message-v2.ts). **Change size**: Modify, Small. **Follows**: DECISIONS D2.

| Lines | Current | Change |
|---|---|---|
| [#L780](../../../prosabuddy-rocq/packages/opencode/src/session/message-v2.ts#L780) | `CACHE_HEAVY_TOOLS = new Set(["read", "grep", "coqtop", "coqc", "coq_session", "checkpoint", ...])` | replace `coqtop`, `coqc`, `coq_session` with `lean_query`, `lean_check`, `lean_session`; add `lsp` (hover output on Mathlib names can be long). |
| [#L781](../../../prosabuddy-rocq/packages/opencode/src/session/message-v2.ts#L781) | `CACHE_PROOF_TOOLS = new Set(["coqtop", "coqc", "coq_session", "checkpoint", "proof_plan"])` | `["lean_query", "lean_check", "lean_session", "checkpoint", "proof_plan"]`. |

These sets decide how much old tool output is kept in the model context. Re-tune the character limits in
`session/prompt.ts` (`cacheProjectionOptions`) after the first Lean runs: Lean goal states and diagnostics are longer
than Rocq ones.
