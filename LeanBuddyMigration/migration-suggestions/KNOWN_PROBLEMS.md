# Known Problems to Settle Before Porting (read this first)

These are structural problems in ProsaBuddy found by running it, not by reading it: 57 runs of the
`replicate-prosa-buddy` replication (CityU PC, gpt-6-luna at effort max and xhigh, 21 case studies, 2026-10-06 to
2026-10-09). Evidence and timelines: `../replicate-prosa-buddy/results/fleet_20261008/PROSABUDDY_ISSUES.md` and
`fleet_20261009_xhigh/PROSABUDDY_ISSUES.md` on the PC (issue codes S1–S32). Code links point at the pure upstream
baseline [`prosabuddy-rocq`](../prosabuddy-rocq/BASELINE.md).

**Status: all items decided (2026-10-09, [DECISIONS.md](DECISIONS.md) D8–D12): the Lean version fixes them by design.**
**Rule for the migration agent:** do not port the mechanisms below one-to-one. Translate a file with its notes
(`tools-advices/`, `gap-revisions/`), then apply the matching **Fix** from [`known-problem-fixes/`](known-problem-fixes/README.md).
Items are ordered by how many runs they decided.

`B` = `../prosabuddy-rocq`

---

## K1. Extra imports are impossible (S15) — becomes a hard blocker in Lean

- **Symptom**: three proofs that Rocq's kernel accepted (axiom-free, statement unchanged, `Qed`) were rejected:
  2007-RTSS-Theorem4, 2015-RTAS-Lemma8, 2007-RTSS-Theorem1. Each needed one more Prosa module. An import inside
  the proof fails the AST audit (`PROOF_SYNTERP_FORBIDDEN`); an import above the theorem is refused by the edit
  guard (`protected_prefix`) and, if forced, fails the audit (`EXTERIOR_AST_CHANGED`). The prompts say imports
  before the theorem are allowed. Lemma8 failed both replication rounds on this alone.
- **Where**: [`protected_prefix` edit rejection, proof-workflow.ts#L1001](../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1001);
  [trusted roots, coq-ast-audit.ts#L54](../prosabuddy-rocq/packages/opencode/src/tool/coq-ast-audit.ts#L54);
  [`PROOF_SYNTERP_FORBIDDEN`, validate_classified_ast.py#L556](../prosabuddy-rocq/scripts/validate_classified_ast.py#L556);
  [`EXTERIOR_AST_CHANGED`, validate_classified_ast.py#L784](../prosabuddy-rocq/scripts/validate_classified_ast.py#L784).
- **Why worse in Lean**: Lean allows `import` only at the top of the file. There is no in-proof workaround, so
  any case that needs a module the dataset file does not import is unprovable under the current policy.
- **Already settled for the Lean benchmark**: [its rules](../../Deliverables/lean-prosa-v06/benchmark/README.md) allow `import` of any module of the
  package (`Prosa.*`, `Mathlib.*`, statement modules, helper modules) in `Solution.lean`. ProsaBuddy's edit guard
  and audit must follow that rule instead of protecting the whole prefix.
- **Decided (general case)**: the same rule as the benchmark — `import` lines of package modules (`Prosa.*`, `Mathlib.*`, statement and helper modules) may be added to the solution file's header; the edit guard allows exactly that change outside the proof, and the gate (D4) checks it.
- **Fix**: [gap-revisions/04-audit-backend/](gap-revisions/04-audit-backend/README.md) (submission stage `REGION_OUTSIDE_EDIT` allows package imports).

## K2. The locked plan allows one repair, and a rejected repair spends it (S8, S9, S16)

- **Symptom**: the main failure mode. 7 of 14 failures in round 1; in round 2 again 2015-book-Theorem18_6,
  2014-RTCSA-Lemma5, 2009-RTSS-Lemma1, 2014-RTCSA-Lemma4, 2005-ECRTS-Theorem6. Lemma helpers escalate with
  `needs_preceding_bridge` (a step must be added before theirs); the prover adds a bridge region; the checkpoint
  then reports "unexpected proof region …" plus "missing plan node …" and stays blocked, because the accepted plan
  cannot gain a node.
- **Where**: [`MAX_PLAN_RECOVERY_GENERATIONS = 1`, proof-workflow.ts#L43](../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L43);
  repair counter set to 1 also for a rejected repair at [#L2806](../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2806) and [#L2836](../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2836).
- **Decided (D9)**: bounded plan amendments — after a `needs_preceding_bridge` escalation the prover may add one bridge node (with dependencies) to the locked plan via `proof_plan` action `amend`; up to 3 accepted amendments per plan; a rejected amendment costs nothing; no free re-planning.
- **Fix**: [known-problem-fixes/proof-workflow.ts-fixes.md](known-problem-fixes/proof-workflow.ts-fixes.md), [proof-plan.ts-fixes.md](known-problem-fixes/proof-plan.ts-fixes.md), [proof-schema.ts-fixes.md](known-problem-fixes/proof-schema.ts-fixes.md), [prover.txt-fixes.md](known-problem-fixes/prover.txt-fixes.md).

## K3. Turn stops cost proof retries (S5, S31, and the new passive-lookup stop)

- **Symptom**: guards end the model's turn and tell it to "resume in a fresh session"; the benchmark runner counts
  each ended turn as a failed attempt. 2009-RTSS-Lemma2-2 lost 6 of 8 retries in ~25 min without one lemma
  dispatch; many runs had 5–10 idle attempts.
- **Where**: [`stalled_wide_fallback`, prompt.ts#L1210](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1210);
  [`materialization_livelock` / `passive_lookup_stagnation`, prompt.ts#L1543](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1543);
  runner no-op ladder [#L937](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L937), [#L1827](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1827).
- **Decided (D5, D8)**: runner side — guard stops, API errors and zero-token attempts never consume a proof retry (separate capped counter); app side — every stop writes a structured `controller_stop` record whose `required_action` is feasible (for a missing bridge: a K2 amendment).
- **Fix**: [gap-revisions/01-prompt.ts-revision.md](gap-revisions/01-prompt.ts-revision.md) item 8, [known-problem-fixes/prompt.ts-fixes.md](known-problem-fixes/prompt.ts-fixes.md), [gap-revisions/05-benchmark-runner/](gap-revisions/05-benchmark-runner/README.md) item 8.

## K4. The prover waits for a lemma assignment that never comes (S23)

- **Symptom**: after a fresh session the prover writes "No `lemma_assignment` … I am waiting for the scheduler's
  next proof-region assignment" and makes no edit; repeated idle attempts drain retries (2014-RTCSA-Lemma4,
  2009-RTSS-Lemma5 in both rounds, 2015-book-Theorem18_6).
- **Where**: prover rule 19 in [proof-projection.ts#L132](../prosabuddy-rocq/packages/opencode/src/session/proof-projection.ts#L132)
  ("the runtime scheduler mechanically enqueues one dependency-ready lemma-owned region …").
- **Decided (D11)**: the scheduler returns an explicit `no_ready_region` result (reason + required action) that is injected into the prover's turn; the prover never waits silently.
- **Fix**: [known-problem-fixes/proof-workflow.ts-fixes.md](known-problem-fixes/proof-workflow.ts-fixes.md), [prompt.ts-fixes.md](known-problem-fixes/prompt.ts-fixes.md), [proof-projection.ts-fixes.md](known-problem-fixes/proof-projection.ts-fixes.md).

## K5. The plan is stored per session (S27)

- **Symptom**: lemma helpers and every fresh main session see "no source-bound decomposition plan exists for the
  current proof session" although the theorem has an accepted plan; fresh sessions re-plan from scratch and lock
  a second plan (2015-book-Theorem18_6: plans locked at 07:56 and again at 08:41). Seen in 10+ runs.
- **Where**: [classifyDecompositionCheckpoint, proof-workflow.ts#L2036-L2049](../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2036) reads `get(sessionID).decomposition_plan`.
- **Decided (D11)**: the plan and queue are keyed by (workspace, file, theorem); child and fresh sessions read the same plan; only K2 amendments change it.
- **Fix**: [known-problem-fixes/proof-workflow.ts-fixes.md](known-problem-fixes/proof-workflow.ts-fixes.md).

## K6. The plan's root goal is compared as text, sensitive to spaces (S30)

- **Symptom**: `bound_root_goal_mismatch` for correct goals that differ only in spaces around `->` and `,`
  (dataset style `tsk->(a,b)` vs `tsk -> (a, b)`); each rejection spends a planning revision; 2009-RTSS-Lemma2-2
  exhausted its planning budget twice in 20 minutes. Present in 19 runs.
- **Where**: [normalizeGoal, proof-plan.ts#L163](../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L163), check at [#L883](../prosabuddy-rocq/packages/opencode/src/tool/proof-plan.ts#L883).
- **Why it matters in Lean**: Lean statements mix `→`/`->`, `∀`/`forall`, `fun x =>`/`λ x,`, binder grouping and
  pretty-printer line breaks; string comparison will fail far more often.
- **Decided (D10)**: root goals are compared by elaboration (definitional equality in the theorem's context, through `lean_session`/Pantograph), with the normalised-text comparison only as a cheap first pass; a formatting-only mismatch never spends a revision.
- **Fix**: [known-problem-fixes/proof-plan.ts-fixes.md](known-problem-fixes/proof-plan.ts-fixes.md), [lean_session-equivalence.md](known-problem-fixes/lean_session-equivalence.md).

## K7. Plan/file metadata drift on labels and statement text (S1, S2, S20, S22)

- **Symptom**: checkpoints blocked by "kind expected semantic_bridge, observed shape_transport", "layer expected
  semantic, observed shape", "target normal form differs from the accepted plan" for regions whose statement is
  equivalent (or the plan's normal form is English prose). Upstream 8e1de8c's new contract parser removes the
  truncation part of this (see proof-workflow note §8), not the label/statement part.
- **Decided (D10)**: `kind`/`layer` are owned by the plan node and no longer re-declared in the file; region targets are compared with `normal_form` by elaboration; prose or non-elaborating `normal_form` is rejected at plan time.
- **Fix**: [known-problem-fixes/proof-workflow.ts-fixes.md](known-problem-fixes/proof-workflow.ts-fixes.md), [proof-plan.ts-fixes.md](known-problem-fixes/proof-plan.ts-fixes.md), [proof-schema.ts-fixes.md](known-problem-fixes/proof-schema.ts-fixes.md).

## K8. The same failed step is re-dispatched indefinitely (S29)

- **Symptom**: 2005-ECRTS-Theorem6 dispatched one step 38 times (one version 16 times), 28 escalations, 0 solved;
  run ended at the 80M token limit.
- **Decided (D11)**: after 3 escalations of the same region with the same escalation type and no addressing source change, the region is not re-dispatched; the scheduler requires a K2 amendment or a remodel.
- **Fix**: [known-problem-fixes/proof-workflow.ts-fixes.md](known-problem-fixes/proof-workflow.ts-fixes.md), [lemma.txt-fixes.md](known-problem-fixes/lemma.txt-fixes.md).

## K9. "Proved" means different things to the runner and to the agent (S28)

- **Symptom**: the runner reported `status=success` for 2007-RTSS-Theorem4 and 2015-RTAS-Lemma8 while ProsaBuddy's
  own final AST audit rejected both; the agent itself said "not yet accepted".
- **Where**: runner [check_proof_success, #L1468](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1468) (Qed + no shortcuts + coqc, no audit) vs the in-agent final theorem gate (coq-ast-audit).
- **Already settled for the Lean benchmark**: [`benchmark/check.py`](../../Deliverables/lean-prosa-v06/benchmark/check.py) is that shared
  definition (frozen files unchanged, forbidden-token scan, `lake build`, fresh statement check, `#print axioms`
  allowing only `propext`, `Classical.choice`, `Quot.sound`). Use it in both the runner and the in-agent final gate.
- **Decided (general case, D4)**: the same five checks implemented in `tool/lean-gate.ts` (frozen files, forbidden tokens, `lake build`, fresh statement check, `#print axioms`); in benchmark mode the gate calls `check.py` itself.
- **Fix**: [gap-revisions/04-audit-backend/](gap-revisions/04-audit-backend/README.md).

## K10. No context compaction for custom provider models (S24)

- **Symptom**: token_limit endings: one attempt of 2005-ECRTS-Theorem6 used ~55M tokens; 2009-RTSS-Lemma2-2
  (round 1) ran out of its 80M budget.
- **Where**: a custom model without `limit.context` gets context 0 ([provider.ts#L897](../prosabuddy-rocq/packages/opencode/src/provider/provider.ts#L897)), and compaction is skipped when context is 0 ([compaction.ts#L52-L56](../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L52)).
- **Decided (D12)**: every model used by a proof agent must declare `limit.context`; session start (and the runner) fail fast otherwise; compaction is tested with real Lean goal states.
- **Fix**: [known-problem-fixes/provider.ts-fixes.md](known-problem-fixes/provider.ts-fixes.md).

## K11. Smaller problems — decided (D12, [DECISIONS.md](DECISIONS.md))

- **Workflow bypass (S14)**: the prover can write a monolithic proof with no regions and never call `checkpoint`
  (2007-RTSS-Theorem1, both rounds). Decided (D12): allowed; the final gate is what counts.
- **Solved state vs source (S26)**: the workflow marked a region solved while the file still had `admit.`; in
  Lean, compute "solved" from the elaborated file (no `sorry` in the region), never from stored state.
- **Stale diagnostics (S25)**: errors from an earlier revision were shown as current; tag every diagnostic with
  the source hash it belongs to.
- **API outage looks like an idle model (S32)**: the runner charged retries while the model API was unreachable;
  distinguish transport errors from model no-ops.
- **LSP tool denied while prompts recommend it**: the runner writes `"lsp": "deny"`
  ([#L888](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L888)),
  but `lemma.txt` tells the helper to use `lsp proofGoals`. Make the Lean prompts list only tools the agent has.

**Decisions for K11 (D12):** workflow bypass is allowed, a checkpoint/gate of the current source is required before
reporting success ([prompt.ts-fixes.md](known-problem-fixes/prompt.ts-fixes.md)); "solved" is recomputed from the source
([proof-workflow.ts-fixes.md](known-problem-fixes/proof-workflow.ts-fixes.md)); diagnostics carry their source hash and stale ones are
dropped ([proof-context.ts-fixes.md](known-problem-fixes/proof-context.ts-fixes.md)); API outages are handled by D5; the `lsp proofGoals`
wording is removed from the prompts ([lemma.txt-fixes.md](known-problem-fixes/lemma.txt-fixes.md), [whole-lemma.txt-fixes.md](known-problem-fixes/whole-lemma.txt-fixes.md), [proof-projection.ts-fixes.md](known-problem-fixes/proof-projection.ts-fixes.md)).
