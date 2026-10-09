<span style="color:red"><strong>Purpose:</strong> Provide a fallback when a proof fails and the cause is unclear: inspect the goal, assumptions and first reliable error; make one small repair, verify it, and preserve successful work. Route recognized goal, parameter, rewriting or counting problems to their specialized skills.</span>

<span style="color:red"><strong>Required backend adaptation:</strong> <a href="#lean-review-2">Proof boundaries</a> cannot be located by Qed./Defined. in Lean. Use Lean syntax and source ranges, keeping the same ownership policy. <a href="#lean-review-6">Completion checks</a> must use current Lean validation evidence. These are recommendations; the original guide is retained.</span>

---
name: rocq-proof-methodology
#<span style="color:red"><strong>description recommendation:</strong> For a future Lean version, describe general Lean proof triage when no specialized skill applies. Reason: the backend changes, while small verified repairs remain useful.</span>
description: Use for general Rocq/Coq proof development and recovery when the blocker is a goal-state, tactic, typing, focus, rewrite, or incomplete-proof issue and no narrower domain skill already explains it.
---

# Rocq Proof Methodology <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Triage proof failures through small verified steps.</span>

Use this skill as a compact recovery loop, not as a second copy of the agent's proof policy. Prefer a narrower skill when the diagnostic already identifies a specific pattern such as goal focus, `by` expansion, failed lemma application, count/bigop bridging, or a known Prosa construction.

<a id="lean-review-1"></a>

## Core loop <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Fix the first reliable error and preserve checked progress.</span>

<span style="color:red"><strong>Why:</strong> A Rocq proof-state session cannot supply Lean goals.<br><strong>Proposed change:</strong> Read goals and diagnostics from the available Lean backend at the current document version; do not assume a tool named lean_session exists.</span>

1. Read the exact current goal and hypotheses from the live proof state.
2. Fix the first reliable error only: syntax/structure, then typing/unification, then tactic failure or unfinished goals.
3. Make one small proof-producing step or edit.

<span style="color:red"><strong>Keep:</strong> Small verified edits, checkpoints and rollback of only the failed tail.<br><strong>Backend adaptation:</strong> Validate Lean source with the project toolchain, for example lake env lean, and attach results to the checked revision.</span>

4. Re-run the smallest relevant goal/checkpoint validation.
5. Persist a validated step in the proof file or roll back only its failing tail.

Do not respond to a failed step with an unrelated broad search. A targeted lookup is justified when the current goal or compiler error names the missing definition, lemma shape, instance, or premise; use its result in the next proof attempt.

<a id="lean-review-2"></a>

## Scope and proof integrity <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Respect proof ownership and preserve theorem premises.</span>

- Keep edits inside the currently owned theorem or proof_region.
- Preserve compiler-certified prefixes and current transaction state.

<span style="color:red"><strong>Why:</strong> Axiom, Parameter, Hypothesis, Variable and Admitted. are Coq declaration forms.<br><strong>Proposed change:</strong> Recognize Lean axiom/variable and sorry as appropriate. Preserve existing premises and the prohibition on adding assumptions or placeholders to bypass proof obligations.</span>

- Do not introduce <span style="color:gray">`Axiom`</span>, <span style="color:gray">`Parameter`</span>, <span style="color:gray">`Hypothesis`</span>, <span style="color:gray">`Variable`</span>, `admit`, or <span style="color:gray">`Admitted.`</span> as a proof substitute. A runtime-authorized temporary skeleton is not final success.
- Do not change theorem assumptions or declarations to make the proof easier.

<span style="color:red"><strong>Why:</strong> Lean has no Qed./Defined. terminator, so a parser based on those commands cannot locate Lean proof boundaries.<br><strong>Proposed change:</strong> Use Lean syntax and source ranges. A parenthesized local by block can be a convention, but character-level bracket counting is not a replacement for parsing. Keep ownership rules.</span>

- <span style="color:gray">Close a benchmark proof only with a real compiling `Qed.` (or `Defined.` when transparency is intentionally required).</span>

<a id="lean-review-3"></a>

## Goal and branch discipline <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Keep branch structure and local proofs explicit.</span>

- Inspect the goal after a tactic that rewrites, applies a lemma, introduces a local fact, or changes branches.

<span style="color:red"><strong>Keep:</strong> Branch isolation and explicit local proof structure. Lean supports braces too; adapt the full declaration syntax rather than removing braces.</span>

- Use bullets or `{ ... }` to isolate multiple focused goals. Repair focus/brace structure before changing semantic tactics.

<span style="color:red"><strong>Why:</strong> SSReflect by adds a closing step; Lean by introduces a tactic proof and cannot simply be removed.<br><strong>Proposed change:</strong> Keep by and inspect separate steps inside it. In a future Lean guide, omit routing to the proposed-to-remove tactics skill; route specific failures to goal, parameter, math or count-bridging.</span>

- If a <span style="color:gray">compressed `by ...`</span> hides the failure, expand only that boundary and inspect the first revealed goal.
- For dependent rewrite errors, first consider `subst` for a variable equality, or revert/generalize dependent hypotheses before rewriting.

<a id="lean-review-4"></a>

## Choosing the next step <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Choose a step suited to the current obligation.</span>

Choose tactics from the actual goal shape; this is guidance, not a mandatory route:

<span style="color:red"><strong>Why:</strong> These Coq tactic names are not the corresponding checked Lean interfaces.<br><strong>Proposed change:</strong> Use rfl for definitional reflexivity and dsimp for the required definitional simplification.</span>

- definitional equality: <span style="color:gray">`reflexivity`</span>, <span style="color:gray">`cbn`</span>, or a small unfold;

<span style="color:red"><strong>Why:</strong> Lean split analyzes if/match expressions; it is not the conjunction constructor used here.<br><strong>Proposed change:</strong> Use constructor for a conjunction goal.</span>

- available hypothesis or constructor: `exact`, `assumption`, `apply`, `constructor`, <span style="color:gray">`split`</span>, `left`, `right`;

<span style="color:red"><strong>Why:</strong> f_equal and congruence name Coq mechanisms.<br><strong>Proposed change:</strong> Use congrArg/congr for function congruence and an appropriate Lean equality procedure for the actual goal.</span>

- equality transport: `rewrite`, `subst`, <span style="color:gray">`f_equal`</span>, <span style="color:gray">`congruence`</span>;

<span style="color:red"><strong>Why:</strong> assert, suff and pose proof use Coq syntax.<br><strong>Proposed change:</strong> Use Lean have or suffices, with the actual binder and proof-block syntax.</span>

- local bridge: `have`, <span style="color:gray">`assert`</span>, <span style="color:gray">`suff`</span>, <span style="color:gray">`pose proof`</span>, or `set`;

<span style="color:red"><strong>Keep:</strong> Select a solver for the actual number domain. The checked Lean version supports lia, and Mathlib supplies ring; migration alone does not require renaming them.</span>

- arithmetic: use the imported solver appropriate to the domain, such as `lia` or `ring`;

<span style="color:red"><strong>Why:</strong> Coq auto/eauto depth and hint-database settings do not configure Lean proof search.<br><strong>Proposed change:</strong> Keep bounded search, but specify the facts and search controls of the chosen real Lean tactic.</span>

- bounded search: <span style="color:gray">`auto n`</span> or <span style="color:gray">`eauto n`</span> only when the relevant <span style="color:gray">hint database</span> and premises are understood.

<span style="color:red"><strong>Why:</strong> These repeated-rewrite forms are SSReflect syntax.<br><strong>Proposed change:</strong> Express any retained restrictions in terms of actual Lean rewriting operations; do not silently relax the original policy.</span>

Do not use ssreflect repeat-rewrite syntax <span style="color:gray">`rewrite !...`</span> or <span style="color:gray">`rewrite -!...`</span> in this environment.

<span style="color:red"><strong>Why:</strong> A ban naming Coq intuition does not specify a Lean tool policy.<br><strong>Proposed change:</strong> Retain the intended explicit logical reasoning; define any Lean-specific restriction narrowly.</span>

Do not use <span style="color:gray">`intuition`</span>; construct the logical steps explicitly.

<a id="lean-review-5"></a>

## Candidate lemma audit <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Check a candidate theorem and all its premises.</span>

Before committing to an imported lemma:

<span style="color:red"><strong>Keep:</strong> Audit the conclusion, arguments and premises.<br><strong>Backend adaptation:</strong> Recheck actual Lean binders, inference and unification in the current context.</span>

1. inspect its exact type;
2. unify its conclusion with the live target;
3. list the remaining premises and implicit instances;
4. check whether each premise follows from current hypotheses or an already certified local bridge;
5. abandon or change the instantiation when a required premise is unavailable.

<span style="color:red"><strong>Keep:</strong> Retry only when relevant evidence changes.<br><strong>Backend adaptation:</strong> Produce and verify application evidence using Lean; fingerprints and certificates need not be renamed.</span>

A verified failed lemma/missing-premise route must not be repeated through cosmetic edits or an `admit_id` rename. It may be reconsidered after a new hypothesis is derived, the missing premise is compiled, the instantiation genuinely changes, or the audit is shown wrong.

<a id="lean-review-6"></a>

## Completion check <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Confirm completion against the latest validated source.</span>

Before reporting success, verify:

- the current owned goal is closed;

<span style="color:red"><strong>Keep:</strong> No placeholder proofs.<br><strong>Backend adaptation:</strong> Check for Lean sorry/sorryAx dependencies as part of validation; ordinary warnings are not automatically proof failures.</span>

- no proof placeholder remains in the owned theorem;

<span style="color:red"><strong>Why:</strong> coqc validates Coq source, not Lean.<br><strong>Proposed change:</strong> Use the project Lean compiler and diagnostics for the authoritative revision. Retain checkpoint policy.</span>

- the authoritative staged revision, not an older disk copy, passes checkpoint/<span style="color:gray">coqc</span>;
- all opened branches and local assertions are closed;

<span style="color:red"><strong>Why:</strong> There is no Lean equivalent of a Qed. terminator.<br><strong>Proposed change:</strong> Check the actual declaration boundary, closed proof obligations and compiler result for the authorized source range.</span>

- <span style="color:gray">the final theorem terminator</span> is correct for the assigned ownership layer.

If the proof still fails, return the exact stable goal/error, the smallest failed step, missing premises, and which certified prefix remains reusable.
