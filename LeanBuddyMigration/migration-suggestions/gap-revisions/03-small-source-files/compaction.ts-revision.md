# Revision: `session/compaction.ts` (context compaction)

**File**: [`session/compaction.ts`](../../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts) (542 lines). **Change size**: Modify, Small. **Follows**: DECISIONS D1, D2; KNOWN_PROBLEMS K10.

| Lines | Current | Change |
|---|---|---|
| [#L95](../../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L95) | `PRUNE_PROTECTED_TOOLS = [..., "coqc", "coqtop", "proof_plan", "coq_session", "checkpoint"]` | `[..., "lean_check", "lean_query", "proof_plan", "lean_session", "checkpoint"]`. |
| [#L228](../../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L228) | "current coq_session/petanque snapshot or tactic position" | "current `lean_session` goal state (handle id is not restorable after a restart, record the goal text and the region)". |
| [#L230](../../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L230), [#L250](../../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L250) | "the current .v file on disk"; "Which .v files, proof_regions, admit IDs …" | ".lean"; same fields. |
| [#L255](../../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L255), [#L263](../../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L263) | "coq_session/petanque … LSP, coqc" | "`lean_session` …, diagnostics, `lean_check`". |
| [#L390](../../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L390) | "Live proof snapshot (… from rocq-lsp)" | Snapshot comes from the `lean_session` goal state (BACKEND_DECISION rule 1); LSP diagnostics only as a revision-tagged extra. |
| [#L52-L56](../../../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L52) | compaction disabled when `model.limit.context === 0` | Unchanged here, but every model in the Lean setup must declare `limit.context` (KNOWN_PROBLEMS K10); the runner should refuse to start a model without it. |

Lean goal states are much longer than Rocq goals (instances, universe levels, implicit arguments); test the compacted
summary with real Lean goals before relying on it.
