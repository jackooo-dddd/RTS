# Fixes: `session/proof-projection.ts`

**File**: [`session/proof-projection.ts`](../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts). **Implements**: D10 (K7), D11 (K4), D12 (LSP wording), D13.

| Location | Current | Change |
|---|---|---|
| prover rule 18a [#L131](../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L131) | "Include owner, admit_id, theorem, kind, target, plan_node, depends_on, source, input, output, layer, expected, normal_form, and grounded `prosa:`, `mathcomp:`, `local:`, `context:`, `coq:`, or `compiler:` evidence" | "Include owner, admit_id, theorem, target, plan_node, depends_on, source, input, output, expected, normal_form, and grounded `prosa:`, `mathlib:`, `local:`, `context:`, `lean:`, or `compiler:` evidence" (D10, D13). |
| prover rule 19 [#L132](../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L132) | "the runtime scheduler mechanically enqueues one dependency-ready lemma-owned region with a complete `lemma_assignment`" | add: "If the runtime reports `no_ready_region`, do the `required_action` it names (for an escalated region needing a bridge: a `proof_plan` amendment); do not wait." |
| [#L238](../../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L238) | "Use `lsp proofGoals` and edit/write LSP diagnostics as first-class proof feedback" | "Use the `lean_session` goal state and the diagnostics attached to edit results as proof feedback; `lsp` is for read-only lookups (hover, definition, references)." (D3) |
