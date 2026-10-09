# Fixes: `agent/prompt/lemma.txt`

**File**: [`agent/prompt/lemma.txt`](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt). **Implements**: D3/D12 (LSP wording), D9 (escalation payload). Apply after `prompt_revision.md` §2.

| Location | Current | Change |
|---|---|---|
| [#L14](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L14) | "`lsp`: use `proofGoals`, hover, definitions, and references from rocq-lsp/coq-lsp" | "`lsp`: read-only hover, definitions, references and symbols" (no goals). |
| [#L84](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L84) | "Inspect the goal with `coq_session goal`, `petanque goals`, or `lsp proofGoals`" | "Inspect the goal with `lean_session`". |
| [#L215](../../prosabuddy-rocq/packages/opencode/src/agent/prompt/lemma.txt#L215) | "Prefer `coq_session`, `petanque`, and `lsp proofGoals`" | "Prefer `lean_session`". |
| escalation fields (`escalation_type: needs_preceding_bridge`, `remodel_request`) | free text | when escalating with `needs_preceding_bridge`, include the missing fact as a Lean proposition (`proposed_bridge`) so the prover can submit it as an amendment directly (D9). |
