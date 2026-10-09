---
name: prosabuddy-guard-recovery
description: Interpret Prosabuddy proof guard, premise-audit, lean_session desynchronization, proof-transaction recovery, scheduler-status, plan-amendment, final-gate, and theorem-region planning feedback and select the next safe proof action. Use when a proof worker receives verified_failed_route_reuse, verified_failed_route_requires_audit, candidate_unresolved_premise, repair_plan_route, revise_amendment, no_ready_region, final_gate_rejected, region-check-rejection, proof_transaction_stale_view, proof_transaction_scope_rejection, session_state_desync, debug-only progress, a recoverable transaction, or region-granularity guidance.
---

# Prosabuddy Guard Recovery

Use the full runtime guard payload as the source of truth. Preserve staged and compiler-validated proof text, then repair only the rejected dimension.

## Recovery Map

| Guard or state | Next safe action |
|---|---|
| `verified_failed_route_reuse` | Change the lemma, affected target route, or mechanically audited instantiation; alternatively prove the exact missing premise with a current compiler certificate. |
| `verified_failed_route_requires_audit` | Replace the legacy name-only candidate with a structured library candidate and let the live premise audit check its exact interface and application. Do not treat a renamed fact or free-form override as evidence. |
| `candidate_unresolved_premise` | A residual premise already survived the live assumption/conversion probe. Produce it through an explicit dependency node or reference a current compiler certificate from the handoff; otherwise remove the candidate. |
| `candidate_premise_*_invalid` | Use the exact residual-premise fingerprint returned by the guard. Correct the dependency target or reference a current matching certificate; do not invent certificate IDs or relabel a residual premise as local evidence. |
| `recommended_action: repair_plan_route` | Preserve the current semantic DAG: keep node targets, edges, dependencies, and the leaf set fixed. Change only the candidate lemma, its mechanically distinct instantiation, or the audited source of a residual premise. |
| `recommended_action: repair_plan_metadata` | Correct only the fields named by `repair_hint` and `details`—for example node IDs, edge endpoints, dependency anchors, declared root targets, or the final composition output. Copy the reported normalized target instead of paraphrasing it. This does not consume a semantic DAG revision. |
| `recommended_action: do_not_retry_metadata_only_plan` | The submitted payload has not changed the review-relevant state. If `metadata_repair_repeat_count` is `5/5`, the identical metadata failure has reached its limit. Do not resubmit the same payload or make another wording-only change; re-read `compared_target_field`, normalized values, and hashes, then rebuild the exact rejected fields from authoritative root/producer data. |
| `recommended_action: revise_semantic_dag` | Submit a materially different dependency/target structure only when the current plan has a structural hard error. The initial plan plus at most four materially distinct revisions is the bounded semantic search space. |
| `recommended_action: stop_and_report_best_plan` | Do not explore another speculative or still-failing semantic DAG. Report the best rejected plan and its exact hard errors. A stale exhausted verdict may be invalidated only by a candidate that now passes the deterministic review; do not keep submitting rejected candidates to test this exception. |
| `recommended_action: materialize_accepted_plan` (with `accepted_plan_locked: true`) | The plan is accepted and locked; a whole-plan resubmission does not change it. Materialize it, or, when a region escalated with a missing preceding fact, submit `proof_plan` with action `amend`. |
| `recommended_action: revise_amendment` | The amendment was rejected and cost nothing; fix the reported hard errors of the bridge node (its Lean statement, candidates, dependencies) and resubmit the amendment. |
| `recommended_action: materialize_amendment` | Write the new bridge region (with its `plan_node`) before the escalated region, give the escalated region's contract the new dependency, and run checkpoint. |
| `amendment_rejected` / "not available" | No region is escalated with a missing fact, the bridge does not go before the escalated region, or all 3 amendments are used. Do not resubmit; follow the reason. |
| `<scheduler-status>` `no_ready_region` | No lemma task will be dispatched until the `required_action` is done (an amendment, a checkpoint, a theorem-level repair, or an explicit wait for a running task). Do it; do not wait for an assignment. |
| region `escalated 3 times … without a source change` | The region is not re-dispatched unchanged. Amend the plan with the missing bridge or remodel the region (new statement or split). |
| `status: final_gate_rejected` | The final gate (frozen statement, forbidden tokens, `lake build`, `#print axioms`) rejected the revision. Remove the construct named by the reason code; never change the statement or text outside the proof. |
| `<region-check-rejection>` | The submission check rejected a region (statement or exterior text changed, forbidden construct, region does not elaborate). Repair the current staged revision from the exact reasons in the same session. |
| `proof_transaction_stale_view` | Re-read the staged region and build a new patch against the current revision. |
| `proof_transaction_scope_rejection` | Shrink the patch to the authorized theorem body or proof region and preserve its markers and surrounding source. |
| `session_state_desync` | Stop running tactics, reopen the assigned region with `lean_session` from the current staged source, and check that the goal matches the region's statement before continuing. |
| `progress_level: debug` | Keep the draft for diagnosis, but do not treat it as route validation or accepted proof progress. |
| recoverable transaction | Use the active recovery baseline. If `recovery_base` is `best_certified`, continue there while preserving the newer unaccepted draft in the journal; otherwise continue from the current staged draft. |

## Generic Route Recipe

Use this only as a soft planning prior:

1. Prepare definitions and local context needed by later facts.
2. Establish a semantic or pointwise bridge.
3. Normalize the data, collection, or library-facing proof shape.
4. Aggregate or compose established facts.
5. Close the final logical or arithmetic step.

Reorder, merge, replace, or abandon these layers when the live goal, hypotheses, premise audit, or compiler evidence supports a better route. Never turn a successful trace into a theorem-specific lemma list, variable naming scheme, or tactic script.

## Region Granularity

Prefer roughly 3-6 meaningful first-level regions, commonly 4-5, without treating the count as a guard condition. Keep several local rewrites, arithmetic steps, or helper facts together when they establish one exported fact under one dependency boundary. Split only for independent semantic layers, missing dependencies, cross-branch ownership, or repeated semantic/compiler failure. Merge adjacent tactic-sized leaves that share hypotheses and have no useful independent certificate.

## Candidate Roles And Scheduling

Set each structured library candidate to `direct_apply`, `rewrite`, `transport`, `local_fact`, or `automation_hint`. Only `direct_apply` is expected to unify with the complete node target and expose residual premises during planning; other roles are checked for availability and validated at their concrete proof use. Follow the runtime's dependency-ready region selection: declared producer regions must be compiler-certified, while file order is only a tie-breaker among ready regions.

## Workflow

1. Read the complete guard payload, including fingerprints, missing premises, transaction revision, recommended action, `repair_hint`, and structured `details`.
2. Preserve the active transaction baseline, every compiler-certified fragment, and any newer unaccepted draft recorded by revision/hash.
3. Change only the route, premise mapping, proof state, or edit scope identified by the guard.
4. Re-read after stale-view or desynchronization errors instead of replaying an old edit or tactic.
5. Validate the new staged revision with the narrowest suitable `lean_session` step, `lean_check`, or `checkpoint`.
6. If the guard omits the evidence needed to choose a legal recovery, report the missing field instead of inventing a free-form override.

The skill supplies stable recovery policy only. Runtime prompts must provide concrete transaction IDs, revisions, hashes, goal fingerprints, failure IDs, and premise fingerprints.
