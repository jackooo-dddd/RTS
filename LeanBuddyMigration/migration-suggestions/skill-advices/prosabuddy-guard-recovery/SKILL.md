<span style="color:red"><strong>Purpose:</strong> Explain how to recover when ProsaBuddy rejects an operation, for example because an edit used an outdated revision. Read the rejection, repair the stated cause and preserve already validated progress. This handles system checks rather than the mathematics of the proof.</span>

<span style="color:red"><strong>Backend adaptation only:</strong> The recovery policy, candidate roles, revision management and dependency scheduling remain valid. Adapt production and verification of <a href="#lean-review-4">premise audits and compiler certificates</a>, and access to <a href="#lean-review-5">proof states</a>, where the implementation depends on Coq. This is not a structural failure of the guard workflow. Original contracts remain unchanged.</span>

---
name: prosabuddy-guard-recovery
#<span style="color:red"><strong>description recommendation:</strong> For a future Lean version, replace Coq-session desynchronization with Lean document/session desynchronization. Reason: state validation changes backend; guard names and recovery policy remain valid.</span>
description: Interpret Prosabuddy proof guard, premise-audit, Coq-session desynchronization, proof-transaction recovery, and theorem-region planning feedback and select the next safe proof action. Use when a proof worker receives verified_failed_route_reuse, verified_failed_route_requires_audit, candidate_unresolved_premise, repair_plan_route, proof_transaction_stale_view, proof_transaction_scope_rejection, session_state_desync, debug-only progress, a recoverable transaction, or region-granularity guidance.
---

# Prosabuddy Guard Recovery <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Recover from a ProsaBuddy guard rejection while preserving progress.</span>

Use the full runtime guard payload as the source of truth. Preserve staged and compiler-validated proof text, then repair only the rejected dimension.

<a id="lean-review-1"></a>

## Recovery Map <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Map each guard response to an allowed recovery action.</span>

<span style="color:red"><strong>Keep:</strong> Guard decisions, revisions, fingerprints, recovery policy and retry limits.<br><strong>Backend adaptation:</strong> If premise probes or certificates contain Coq-specific evidence, produce and validate equivalent evidence in the current Lean context. The workflow itself does not need structural replacement.</span>

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
| `proof_transaction_stale_view` | Re-read the staged region and build a new patch against the current revision. |
| `proof_transaction_scope_rejection` | Shrink the patch to the authorized theorem body or proof region and preserve its markers and surrounding source. |
| `session_state_desync` | Stop submitting tactics, reopen the assigned region-scoped session, and verify the goal fingerprint before continuing. |
| `progress_level: debug` | Keep the draft for diagnosis, but do not treat it as route validation or accepted proof progress. |
| recoverable transaction | Use the active recovery baseline. If `recovery_base` is `best_certified`, continue there while preserving the newer unaccepted draft in the journal; otherwise continue from the current staged draft. |

<a id="lean-review-2"></a>

## Generic Route Recipe <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Offer a flexible route for planning proof work.</span>

Use this only as a soft planning prior:

1. Prepare definitions and local context needed by later facts.
2. Establish a semantic or pointwise bridge.
3. Normalize the data, collection, or library-facing proof shape.
4. Aggregate or compose established facts.
5. Close the final logical or arithmetic step.

<span style="color:red"><strong>Keep:</strong> This is a language-independent planning heuristic; let the actual Lean goal determine which stages are useful.</span>

Reorder, merge, replace, or abandon these layers when the live goal, hypotheses, premise audit, or compiler evidence supports a better route. Never turn a successful trace into a theorem-specific lemma list, variable naming scheme, or tactic script.

<a id="lean-review-3"></a>

## Region Granularity <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Choose proof regions by meaning and dependencies.</span>

<span style="color:red"><strong>Keep:</strong> Semantic regions and dependency-based ownership.<br><strong>Backend adaptation:</strong> If boundaries are parsed from Coq terminators, use Lean syntax/source ranges instead. Validate a region in its enclosing declaration and context.</span>

Prefer roughly 3-6 meaningful first-level regions, commonly 4-5, without treating the count as a guard condition. Keep several local rewrites, arithmetic steps, or helper facts together when they establish one exported fact under one dependency boundary. Split only for independent semantic layers, missing dependencies, cross-branch ownership, or repeated semantic/compiler failure. Merge adjacent tactic-sized leaves that share hypotheses and have no useful independent certificate.

<a id="lean-review-4"></a>

## Candidate Roles And Scheduling <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Assign candidate roles and schedule validated dependencies.</span>

Set each structured library candidate to `direct_apply`, `rewrite`, `transport`, `local_fact`, or `automation_hint`.

<span style="color:red"><strong>Keep:</strong> Candidate roles and the direct_apply premise-audit contract.<br><strong>Backend adaptation:</strong> Obtain binders, inferred arguments and premise checks from Lean; a declaration name alone is not applicability evidence.</span>

Only `direct_apply` is expected to unify with the complete node target and expose residual premises during planning; other roles are checked for availability and validated at their concrete proof use.

<span style="color:red"><strong>Keep:</strong> Dependency scheduling after producer validation.<br><strong>Backend adaptation:</strong> Generate and verify compiler certificates against the actual Lean environment and source revision.</span>

Follow the runtime's dependency-ready region selection: declared producer regions must be compiler-certified, while file order is only a tie-breaker among ready regions.

<a id="lean-review-5"></a>

## Workflow <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Read feedback, repair the cause and validate the current revision.</span>

1. Read the complete guard payload, including fingerprints, missing premises, transaction revision, recommended action, `repair_hint`, and structured `details`.
2. Preserve the active transaction baseline, every compiler-certified fragment, and any newer unaccepted draft recorded by revision/hash.
3. Change only the route, premise mapping, proof state, or edit scope identified by the guard.
4. Re-read after stale-view or desynchronization errors instead of replaying an old edit or tactic.

<span style="color:red"><strong>Why:</strong> coq_session and coqc cannot execute or validate Lean proofs.<br><strong>Proposed change:</strong> Connect the same recovery workflow to available Lean goal/diagnostic interfaces and the project compiler, for example lake env lean. Adapt state snapshots where backend-specific; do not invent a tool name.</span>

5. Validate the new staged revision with the narrowest suitable <span style="color:gray">`coq_session`</span>, checkpoint, or <span style="color:gray">`coqc`</span> certificate.
6. If the guard omits the evidence needed to choose a legal recovery, report the missing field instead of inventing a free-form override.

The skill supplies stable recovery policy only.

<span style="color:red"><strong>Keep:</strong> Runtime-owned identity, revision and fingerprint fields.<br><strong>Backend adaptation:</strong> Change expression serialization or evidence production only where it depends on Coq; preserve the contracts and policies.</span>

Runtime prompts must provide concrete transaction IDs, revisions, hashes, goal fingerprints, failure IDs, and premise fingerprints.
