# Fixes: `session/proof-context.ts` (diagnostics shown to the agent)

**File**: [`session/proof-context.ts`](../../prosabuddy-rocq/packages/opencode/src/session/proof-context.ts). **Implements**: D12 (S25 stale diagnostics). Apply after `tools-advices/05-session-workflow/proof-context-revision.md`.

- **Location**: diagnostics collection [#L79-L113](../../prosabuddy-rocq/packages/opencode/src/session/proof-context.ts#L79) (touch file, wait for diagnostics, `LSP.diagnostics()`).
- **Change**: record the source hash the diagnostics were computed for (the staged revision sent to Lean LSP); when building the agent-visible snapshot, drop diagnostics whose hash differs from the current staged source hash, and say so ("diagnostics pending for revision …") instead of showing old errors as current.
