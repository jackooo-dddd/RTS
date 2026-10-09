# Fixes: `session/prompt.ts`

**File**: [`session/prompt.ts`](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts). **Implements**: KNOWN_PROBLEMS K3 (app side), D11 (K4), D12 (S14).
Apply after `gap-revisions/01-prompt.ts-revision.md`.

- **K3** — every controller stop names a **feasible** action. In `stalled_wide_fallback` [#L1210](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1210) and the livelock / passive-lookup stop [#L1543-L1565](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1543): when the blocker is an escalated region needing a bridge, the `required_action` is "submit a `proof_plan` amendment for <admit_id>" (D9), never "make a theorem-level edit" against a locked plan. The structured `controller_stop` record (gap-revisions §1 item 8) carries it.
- **K4** — inject the scheduler's `no_ready_region` result (proof-workflow fixes) as a `<scheduler-status>` block at the start of the prover's turn, next to `lemmaContinuationPrompt` [#L324](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L324), including `reason` and `required_action`. Never leave the prover with neither an assignment nor a reason.
- **S14** — direct (non-segmented) proving is allowed (D12); before the prover may report success, require that a checkpoint/final gate of the current source hash has run.
