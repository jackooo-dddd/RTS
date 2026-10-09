# Revision: `agent/agent.ts` (agent definitions and permissions)

**File**: [`agent/agent.ts`](../../../prosabuddy-rocq/packages/opencode/src/agent/agent.ts) (366 lines). **Change size**: Modify, Small. **Follows**: DECISIONS D2, D3, D6.

| Agent (lines) | Current | Change |
|---|---|---|
| `prover` [#L77-L106](../../../prosabuddy-rocq/packages/opencode/src/agent/agent.ts#L77) | description "Layer 1 Coq theorem prover" (L80); allows `coqc`, `coqtop`, `coq_session` (L91-L94) | "Layer 1 Lean theorem prover"; allow `lean_check`, `lean_query`, `lean_session`; **add `lsp: "allow"`** (read-only lookups, D3). |
| `explorer` [#L107-L126](../../../prosabuddy-rocq/packages/opencode/src/agent/agent.ts#L107) | read-only: grep/glob/read; description "locating Coq lemmas" (L121) | "locating Lean/Mathlib/Prosa declarations"; **add `lsp: "allow"` and `lean_query: "allow"`** (both read-only). |
| `whole-lemma` [#L127-L156](../../../prosabuddy-rocq/packages/opencode/src/agent/agent.ts#L127) | `coqc`, `coqtop`, `coq_session`, `lsp`, `petanque` (L140-L144) | `lean_check`, `lean_query`, `lean_session`, `lsp`; delete `petanque` (merged into `lean_session`, D1). |
| `lemma` [#L157-L189](../../../prosabuddy-rocq/packages/opencode/src/agent/agent.ts#L157) | description "uses Coq/LSP tools" (L160); same tool list (L170-L174) | "uses Lean tools"; same renaming as whole-lemma; keep `lsp`. |
| `fixer` [#L190-L217](../../../prosabuddy-rocq/packages/opencode/src/agent/agent.ts#L190) | `coqc`, `coqtop`, `coq_session` (L201-L203) | `lean_check`, `lean_query`, `lean_session`. |
| `diagnoser` [#L218-L243](../../../prosabuddy-rocq/packages/opencode/src/agent/agent.ts#L218) | "Classifies Coq failures" (L220); `coqtop` (L229) | "Classifies Lean failures"; `lean_query`. |

The `lsp` tool itself must expose only hover / go-to-definition / references / document symbols / workspace
symbols (D3); remove `proofGoals` from `tool/lsp.ts` (tools-advices `02-adapted-tools/lsp-revision.md`).
Agent prompts (`PROMPT_PROVER` etc.) are covered by `prompt-advices/prompt_revision.md`.
