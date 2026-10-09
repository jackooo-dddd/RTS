# Fixes: `session/proof-workflow.ts`

**File**: [`session/proof-workflow.ts`](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts). **Implements**: DECISIONS D9 (K2), D11 (K4, K5, K8), D10 (K7), D12 (S26).

**K2 — bounded plan amendments | Modify, Medium**

- **Location**: `MAX_PLAN_RECOVERY_GENERATIONS = 1` [#L43](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L43); `acceptedPlanRepairEvidence` [#L2616](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2616); repair-counter checks [#L2674](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2674), [#L2727](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2727), [#L2785](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2785); counter set to 1 also on a rejected repair [#L2806](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2806), [#L2836](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2836).
- **Change**: replace the single `repair_revision_number` with `accepted_amendments: number` (max 3, D9) and `pending_amendment?`. Increment only when an amendment is **accepted** and materialised; a rejected amendment leaves state unchanged (removes S8/S16). An escalation with `needs_preceding_bridge` (or a remodel request naming a missing preceding fact) marks the region `awaiting_amendment` and is the only trigger that unlocks an amendment.

**K5 — plan keyed by (file, theorem) | Modify, Medium**

- **Location**: in-memory `cache` keyed by session [#L487](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L487); `get(sessionID)` [#L2409](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2409); `statesForFile(file)` already reads all sessions' rows for a file [#L2423](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2423); `classifyDecompositionCheckpoint` reads `get(sessionID).decomposition_plan` and reports "no source-bound decomposition plan exists" [#L2036-L2049](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2036).
- **Change**: a lookup `planFor(file, theorem)` that returns the accepted plan from any session bound to the same file and theorem (newest accepted wins; use `statesForFile`); every reader of `decomposition_plan` (checkpoint classification, materialization review, scheduler) uses it. A lemma child or a fresh main session therefore sees the plan; only the plan's owner session may write it, and only through amendments.

**K4 — explicit `no_ready_region` | Modify, Small**

- **Location**: `planNextSubtask` [#L7651](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L7651), `suggestNextSubtask` [#L8114](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L8114) (returns `undefined` in many branches, e.g. empty queue, active repair).
- **Change**: return a result type `{ kind: "assignment", … } | { kind: "no_ready_region", reason, required_action, admit_ids }`. Reasons: all remaining regions escalated (required action: amendment for region X, D9), waiting for validation (required action: run checkpoint), active repair owned by another session (required action: none, wait is explicit and bounded). `session/prompt.ts` injects it (see `prompt.ts-fixes.md`).

**K7 — labels owned by the plan; statements compared by elaboration | Modify, Small**

- **Location**: materialization review [#L1930-L1955](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1930) (`kind expected …, observed …`, `layer expected …`, `target normal form differs …`).
- **Change**: do not compare `kind`/`layer` with the file at all (the file no longer declares them, D10); compare `normal_form` with the region target through the equivalence service (`lean_session-equivalence.md`), not `normalizedMetadataText`. A non-equivalent target is drift; an unprovable equivalence check (backend error) is a tool error, not drift.

**K8 — stop re-dispatching a repeatedly escalated region | Modify, Small**

- **Location**: escalation recording [#L5984-L6018](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L5984); dispatch gate `assertProofTaskDispatchAllowed` [#L6671](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L6671).
- **Change**: store per region `escalations: { type, source_hash }[]`. If the last 3 entries have the same `type` and the region's source hash has not changed since the first of them, the region becomes `blocked_repeated_escalation`; the dispatch gate refuses it and the scheduler returns `no_ready_region` with required action "amendment (D9) or remodel".

**S26 — "solved" is recomputed from the source | Modify, Small**

- **Location**: `refresh(sessionID, file, source)` [#L3248](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L3248) and queue status carry-over (e.g. [#L2298](../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2298)).
- **Change**: before any scheduling or completion decision, recompute each region's status from the current staged source: solved ⇔ the region contains no `sorry` and the last `lean_check` of this source hash reports no error inside it. Stored statuses are a cache only.
