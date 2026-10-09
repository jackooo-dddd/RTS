<span style="color:red"><strong>Purpose:</strong> Keep the agent working on the goal it intends to prove. After a split or a local fact, check the actual branch and assumptions so that an unfinished local proof is not mistaken for a return to the main theorem.</span>

<span style="color:red"><strong>Proposed removal:</strong> <a href="#lean-review-6">Hard Recovery Protocol</a>. Its goal-count test is too strong in both languages: constructor on a goal P ∧ Q legitimately creates two goals. That is an original-skill issue, not a Lean-only failure. Lean also has no Abort. command. A future version should recover only when the active branch or source state differs from the intended one.</span>

<span style="color:red"><strong>Proposed adaptation:</strong> <a href="#lean-review-1">Triggers</a> and <a href="#lean-review-10">historical traces</a> need actual Lean evidence. Coq case creates branches; Lean case selects existing ones, while cases/by_cases create them. Keep the proof discipline. Original rules and examples remain unchanged.</span>

---
name: goal-focus-discipline
#<span style="color:red"><strong>description recommendation:</strong> For a future Lean version, describe unexpected branch or unfinished-local-proof states using actual Lean diagnostics. Reason: Coq focus messages and branch syntax do not transfer.</span>
description: 'Handle Coq and ssreflect proof-state drift by checking the current number of goals after every tactic that can split or close goals, using bullets to manage branches, and proving any have-generated sublemma inside braces before returning to the main line.'
#<span style="color:red"><strong>argument-hint recommendation:</strong> Keep the requested goal, previous tactic and branch information; obtain it from the actual Lean backend in a future version.</span>
argument-hint: 'Describe the current goal count, the previous tactic, and the branch or sublemma that introduced the drift.'
user-invocable: true
---

# Goal Focus Discipline <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Keep the actual goal aligned with the intended proof step.</span>

<a id="lean-review-1"></a>

## When to Use <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Recognize possible branch or local-proof confusion. | substantial adaptation</span>

<span style="color:red"><strong>Why:</strong> This is a Coq-specific focus error, not a Lean trigger.<br><strong>Proposed change:</strong> Use the Lean diagnostic and goals at its source position. Two goals after constructor on a conjunction are normal.</span>

- <span style="color:gray">Coq reports `Expected a single focused goal but 2 goals are focused.`</span>

<span style="color:red"><strong>Why:</strong> Coq case creates branches; Lean case selects an existing branch. Lean split handles if/match rather than constructing a conjunction, and ordinary negation needs no negP reflection.<br><strong>Proposed change:</strong> Use cases/by_cases, constructor, and intro according to the goal.</span>

- A proof used to have one main line, then <span style="color:gray">`case`</span>, `have`, <span style="color:gray">`apply/negP`</span>, <span style="color:gray">`split`</span>, or <span style="color:gray">`destruct`</span> was added and later tactics stopped fitting.
- The model starts adding extra lemmas instead of first checking whether the proof state already drifted.
- A local fact such as `PENDING0` or `SLOT_BOUND` is introduced, and later tactics behave as if the main goal were still the only goal.

<span style="color:red"><strong>Why:</strong> Both the focus message and case command describe Coq behavior.<br><strong>Proposed change:</strong> Describe an observed Lean failure and inspect the branches produced by cases/by_cases.</span>

- <span style="color:gray">The focus error</span> appears right after <span style="color:gray">`case`</span> or another boolean split, but the split target may still be hidden under a named definition or wrapper.
- A branch "looks done" because the last line rewrote a local hypothesis, but the enclosing goal was never explicitly discharged.

<a id="lean-review-2"></a>

## Core Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Inspect the current goals before continuing. | moderate adaptation</span>
Do not choose the next tactic from proof intent alone. First check how many goals exist now, and whether the previous tactic opened or closed any goal.

If there is more than one goal, switch to bullet management immediately. Do not continue with a single-goal script.

If `have` is used to introduce a lemma, prove it inside `{ ... }` and return only after that local proof is closed.

<span style="color:red"><strong>Why:</strong> Lean case selects a branch instead of creating one.<br><strong>Proposed change:</strong> Use cases for data and by_cases for a proposition.</span>

If a <span style="color:gray">`case`</span>, <span style="color:gray">`destruct`</span>, or reflected boolean split targets a term that is still hidden under a named definition, unfold first. Otherwise the split can create branches without actually changing the enclosing goal.

If the last useful line of a branch only rewrites inside a local hypothesis, do not assume the branch is closed.

<span style="color:red"><strong>Why:</strong> exact: is SSReflect syntax; the explicit-closure principle remains valid.<br><strong>Proposed change:</strong> Use exact h, simpa using h, or exfalso followed by exact hFalse.</span>

Explicitly consume that hypothesis with `exact`, `apply`, or <span style="color:gray">`exfalso; exact:`</span> if it is meant to close the enclosing goal.

When the visible script structure and the live proof state disagree, trust the live proof state. Do not keep editing as if braces, bullets, or a finished-looking `have` block had already restored focus.

If the current focused goal count is not exactly one, the next step is a recovery step, not a math step.

Recovery-step whitelist when the goal count is not exactly one:
- inspect the current goals
- introduce or finish bullets
- close the current `{ ... }` subproof
- return to the parent branch
- abort and restart a noisy exploratory branch

Until focus returns to exactly one intended goal, do not:

<span style="color:red"><strong>Why:</strong> suff is SSReflect syntax.<br><strong>Proposed change:</strong> Use Lean suffices for the same sufficient-condition argument.</span>

- add a new `have`, <span style="color:gray">`suff`</span>, or helper lemma
- attempt a new `rewrite`, `apply`, `exact`, or arithmetic step for the outer theorem
- treat downstream messages such as missing hypotheses, reused names, or failed lemma applications as the main problem

<span style="color:red"><strong>Why:</strong> These historical Coq error strings cannot classify Lean failures.<br><strong>Proposed change:</strong> Use actual Lean diagnostics together with source positions and goals.</span>

Errors such as <span style="color:gray">`Cannot apply lemma ...`</span>, <span style="color:gray">`No such goal`</span>, <span style="color:gray">`... already used`</span>, and <span style="color:gray">`The variable ... was not found`</span> are often secondary effects of proof-state drift once multiple goals are live. Do not repair them before restoring focus.

<a id="lean-review-3"></a>

## Required Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Check the last step, current branch and remaining obligations. | moderate adaptation</span>
1. Read the current proof state before the next step.
   - Record the exact number of focused goals.
   - Record the shape of the current goal.
2. Inspect the previous tactic.
   - Did it split the proof into branches?
   - Did it create a local subgoal?
   - Did it close a branch?

3. Inspect the literal goal head before any new split.

  <span style="color:red"><strong>Why:</strong> Coq case/destruct do not have the same syntax and role as Lean case.<br><strong>Proposed change:</strong> Use cases/by_cases to create the required branches.</span>

  - If the next <span style="color:gray">`case`</span>, <span style="color:gray">`destruct`</span>, or reflection step targets a term hidden under a definition, unfold first.
  - Do not split on mathematical intent alone. Check whether the split target literally occurs in the current goal or active hypothesis.

4. If the goal count changed, respond structurally, not mathematically.
   - New branch: introduce a bullet.
   - Local lemma from `have`: open `{ ... }`, finish it, then return.
   - Closed branch: verify that focus returned to the intended outer goal.
5. When a branch seems finished, verify that the last line actually discharged the enclosing goal.
  - Rewriting inside `Hlt_succ`, `Hdone`, or another local fact is not the same as closing the branch.

  <span style="color:red"><strong>Why:</strong> The colon in exact: is SSReflect syntax.<br><strong>Proposed change:</strong> Use exact h or simpa using h to close the branch explicitly.</span>

  - If the branch should end from that fact, finish with `exact`, `apply`, or <span style="color:gray">`exfalso; exact:`</span>.
6. Only after focus is stable should you pick the next rewriting or reasoning step.
7. Do not add bridge lemmas, arithmetic lemmas, or helper facts just to avoid a focus problem. Fix the branch structure first.

<a id="lean-review-4"></a>

## Hidden Goal Head Before Case Split <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Inspect definitions that hide the intended split. | substantial adaptation</span>
This is a common local cause of fake branch progress.

Pattern:

- the goal is a named wrapper such as `job_misses_no_deadline j`

<span style="color:red"><strong>Why:</strong> Coq case Hdone creates cases and records an equation; Lean case only selects an existing branch.<br><strong>Proposed change:</strong> For a Bool-valued completed definition, use <code>cases hDone : completed ...</code> and inspect the false/true branches.</span>

- the script does <span style="color:gray">`case Hdone: (completed ...)`</span>

<span style="color:red"><strong>Why:</strong> SSReflect by [] performs compact closure; Lean by begins a proof block.<br><strong>Proposed change:</strong> Keep Lean by and finish the actual branch with suitable rfl, simp, assumption or domain facts.</span>

- the first branch ends with <span style="color:gray">`by []`</span>

<span style="color:red"><strong>Why:</strong> This focus message is evidence from a Coq run.<br><strong>Proposed change:</strong> Use the actual Lean diagnostic and unclosed branch instead of predicting the same message.</span>

- the second branch later reports <span style="color:gray">`Expected a single focused goal but 2 goals are focused.`</span>

What happened:

- the split target was not yet the literal head of the goal

<span style="color:red"><strong>Why:</strong> The described branch creation is Coq case behavior.<br><strong>Proposed change:</strong> Use cases/by_cases, then inspect whether the branch equation or assumption simplifies the goal.</span>

- the <span style="color:gray">`case`</span> created branches, but did not rewrite the enclosing goal the way the script expected
- the first branch did not truly close, even if it looked trivial

Hard rule:

- before splitting a boolean goal, check whether the boolean expression is literally present in the current goal head
- if the head is still a wrapper definition, unfold first

Preferred repair:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>Purpose:</strong> Unfold the deadline condition and start the contradiction argument.<br><strong>Proposed Lean adaptation:</strong> Use the actual RTS Classic declarations and Lean unfold/by_contra as appropriate. A genuinely Bool-valued condition still requires its true-value relation; do not mechanically translate negP.</span>

```coq
rewrite /job_misses_no_deadline.
apply/negP => Hnot_done.
...
```

Acceptable repair if you still want a split:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>Purpose:</strong> Split on whether the job is completed and record the branch equation.<br><strong>Proposed Lean adaptation:</strong> Use Lean cases with an equation for the actual Bool-valued completed definition, then prove the false/true branches using the real RTS signature.</span>

```coq
rewrite /job_misses_no_deadline.
case Hdone: (completed job_cost sched j (job_arrival j + job_deadline j)).
- by rewrite Hdone.
- have Hnot_done : ~~ completed job_cost sched j (job_arrival j + job_deadline j).
   by rewrite Hdone.
  ...
```

<span style="color:red"><strong>Why:</strong> case Hdone and by [] are Coq/SSReflect constructs.<br><strong>Proposed change:</strong> Record cases with Lean cases, then close each branch using the actual goal.</span>

Do not write <span style="color:gray">`case Hdone: ...`</span> against a hidden goal head and then trust <span style="color:gray">`by []`</span> to close the first branch.

<a id="lean-review-5"></a>

## Explicit Branch Closure Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Explicitly finish the goal after deriving a useful hypothesis. | minor adaptation</span>
A branch is not closed just because its last line simplified a local hypothesis.

Typical bad shape:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>Purpose:</strong> Show an incomplete branch that rewrites a hypothesis without submitting it to the goal.<br><strong>Proposed Lean adaptation:</strong> If a Lean counterexample is later written, preserve this teaching failure and display its actual remaining goal. Do not turn it into a successful proof or invent an error message.</span>

```coq
have Hlt_succ : x < n + 1.
{
  ...
}
by rewrite addn1 in Hlt_succ.
```

This rewrites `Hlt_succ`, but it may not consume it to solve the enclosing goal `x <= n`.

Preferred repair:

<a id="lean-review-code-4"></a>

<span style="color:red"><strong>Purpose:</strong> Close the preceding branch by explicitly using the derived bound.<br><strong>Proposed Lean adaptation:</strong> Use have with a by block and exact/simpa. Ordinary Nat inequalities are Prop; omega can derive the non-strict bound from the strict successor bound.</span>

```coq
have Hlt_succ : x < n + 1.
{
  ...
}
rewrite addn1 ltnS in Hlt_succ.
exact: Hlt_succ.
```

Contradiction branches should also close explicitly:

<a id="lean-review-code-5"></a>

<span style="color:red"><strong>Purpose:</strong> Combine contradictory facts and close the branch by False.<br><strong>Proposed Lean adaptation:</strong> For actual Prop hypotheses, use exact False.elim (hNot h). If the source facts are Bool-valued, first respect their real definition or truth-value equations.</span>

```coq
exfalso.
exact: (Hnlt Hlt).
```

If the branch closes by contradiction, end it with the contradiction. Do not leave the contradiction only implicit in a rewritten hypothesis.

<a id="lean-review-6"></a>

## Hard Recovery Protocol <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Recover from suspected focus drift; protocol proposed for removal.</span>

<span style="color:red"><strong>Proposed removal:</strong> Do not port this protocol. Multiple goals are legitimate in both languages, and Lean has no Abort. terminator. Retain goal inspection and revision recovery, but base recovery on an actual branch/state mismatch. See the separate original-skill issues review.</span>

Apply this protocol as soon as the goal count is not exactly one.

1. Freeze theorem progress.
  - Do not choose the next tactic from the intended mathematics.
  - Do not edit for convenience or proof style.
2. Read the live state.
  - Record the number of focused goals.
  - Record which goal is the active one.
  - Record the immediately preceding tactic that changed the state.
3. Classify the most recent structural event.

  - <span style="color:gray">`case`</span>, <span style="color:gray">`elim`</span>, <span style="color:gray">`destruct`</span>, <span style="color:gray">`split`</span>, reflection, or another branch opener
  - `have` or <span style="color:gray">`suff`</span> opening a local subproof
  - closing a branch or returning from a local proof
4. Repair structure before content.
  - Missing bullet: insert the bullet and finish that branch.
  - Unclosed local proof: stay inside `{ ... }` until it is discharged.
  - Wrong branch: return to the correct parent branch before doing anything else.

  - Noisy exploratory branch: <span style="color:gray">`Abort.`</span> it and restart from the last stable point.
5. Re-check the live state.

  - If the goal count is still not exactly one, repeat this protocol.
  - If the goal count is exactly one, only then resume rewriting or theorem application.

Exit condition:

- You may resume ordinary proof search only when there is exactly one focused goal and you can name which branch or outer theorem goal you are in.

<a id="lean-review-7"></a>

## Bullet Policy <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Organize branches and local proofs separately. | moderate adaptation</span>

<span style="color:red"><strong>Why:</strong> The branch discipline is reusable, but the commands and Coq bullets differ.<br><strong>Proposed change:</strong> Use cases, induction or constructor as appropriate, and Lean bullets or case labels. Lean also supports braces; do not classify braces themselves as incompatible.</span>

- Use bullets immediately after any tactic that creates multiple branches, such as <span style="color:gray">`case`</span>, <span style="color:gray">`elim`</span>, <span style="color:gray">`destruct`</span>, <span style="color:gray">`split`</span>, or a case analysis hidden inside a boolean reflection step.
- Keep one bullet level per structural split.
- Finish each bullet completely before returning to the parent bullet.
- If a branch contains a local lemma, prove it inside braces within that branch.
- If a branch ends from a local inequality or contradiction fact, close it explicitly instead of relying on a final rewrite in that fact.

Template:

<a id="lean-review-code-6"></a>

<span style="color:red"><strong>Purpose:</strong> Handle zero and successor cases of the service amount.<br><strong>Proposed Lean adaptation:</strong> Use cases with a recorded equation and Nat zero/succ branches; replace the SSReflect simplification suffix with suitable Lean simplification.</span>

```coq
case E: (service_at sched j0 t) => [|k] /=.
- (* branch 1 *)
  ...
- (* branch 2 *)
  ...
```

Local sublemma template:

<a id="lean-review-code-7"></a>

<span style="color:red"><strong>Purpose:</strong> Prove a local fact that the job has arrived but is not yet completed.<br><strong>Proposed Lean adaptation:</strong> Use a Lean local have proof and the real RTS pending signature. Classic pending is Bool-valued; ordinary interval inequalities need no MathComp reflection.</span>

```coq
have PENDING0 : forall t, a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t.
{
  move=> t /andP [GE LT].
  apply/andP; split.
  - by rewrite /has_arrived GE.
  - apply/negP => COMPt.
    ...
}
```

The braces are not cosmetic. They guarantee that the `have` proof is discharged before the main proof resumes.

<a id="lean-review-8"></a>

## Goal-Count Checklist <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Check which branch and local proof are active. | moderate adaptation</span>
Before every nontrivial tactic, ask these questions.

<span style="color:red"><strong>Why:</strong> The checklist names Coq case/split operations.<br><strong>Proposed change:</strong> Use the actual Lean operations cases/by_cases/constructor. Keep goal counts as observations, not automatic failure tests.</span>

```text
How many focused goals exist right now?
What did the previous tactic do to that number?
Am I still in the same branch as one line ago?
If this is a `have`, is its proof isolated in `{ ... }`?
If this is a `case` or `split`, did I introduce bullets immediately?
Does the next split target literally occur in the current goal head?
Do I need to unfold a wrapper definition before splitting?
Did the last branch-ending line explicitly consume the closing hypothesis?
```

If any answer is unclear, stop and inspect the proof state before editing further.

<a id="lean-review-9"></a>

## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">List patterns that obscure branch completion. | substantial adaptation</span>

- Do not keep writing linear tactics after a branching tactic created multiple goals.
- Do not patch a focus problem by introducing another helper lemma.
- Do not start a `have` proof inline and then continue the outer script before the local proof is clearly finished.

<span style="color:red"><strong>Why:</strong> negP is a Bool-reflection view; ordinary Lean negation is a proposition.<br><strong>Proposed change:</strong> Use intro for a negation goal. Handle a genuinely Bool-valued condition through its actual definition.</span>

- Do not assume <span style="color:gray">`apply/negP`</span> is harmless; it can change the goal shape and the remaining branch structure.

<span style="color:red"><strong>Why:</strong> Lean case does not create a case split.<br><strong>Proposed change:</strong> Use cases for a data value, or by_cases for a proposition.</span>

- Do not <span style="color:gray">`case`</span> on a boolean term that is still hidden under a named goal definition.

<span style="color:red"><strong>Why:</strong> The Coq bullet and SSReflect by [] closure are not Lean branch syntax.<br><strong>Proposed change:</strong> Use a Lean bullet or case label and an appropriate proof of that branch.</span>

- Do not trust <span style="color:gray">`+ by [].`</span> unless the preceding split actually rewrote the enclosing goal.

<span style="color:red"><strong>Why:</strong> Lean uses at rather than Coq in to target a hypothesis.<br><strong>Proposed change:</strong> Use <code>rw [hEq] at Hfoo</code> or simp at Hfoo, then explicitly use the result if the goal remains open.</span>

- Do not end a branch with <span style="color:gray">`rewrite ... in Hfoo`</span> and assume the enclosing goal is solved; explicitly use `Hfoo`.

<span style="color:red"><strong>Why:</strong> The contradiction method remains valid; exact: is SSReflect syntax.<br><strong>Proposed change:</strong> Use exfalso followed by exact hFalse, or exact False.elim hFalse.</span>

- Do not leave a contradiction branch "morally finished"; close it with <span style="color:gray">`exfalso; exact: ...`</span> or the equivalent explicit consumer.

<span style="color:red"><strong>Why:</strong> This classification refers to a particular Coq error.<br><strong>Proposed change:</strong> Re-establish the diagnosis from actual Lean output and its location.</span>

- Do not treat <span style="color:gray">`Expected a single focused goal but 2 goals are focused`</span> as a syntax error. It is a proof-structure error.
- Do not trust the text layout of the script over the live session state.

<span style="color:red"><strong>Why:</strong> These strings belong to Coq diagnostics.<br><strong>Proposed change:</strong> Use observed Lean messages with their corresponding contexts.</span>

- Do not respond to secondary errors like <span style="color:gray">`Cannot apply lemma ...`</span> or <span style="color:gray">`No such goal`</span> before restoring the goal count to one.
- Do not keep a branch open just because the surrounding code already looks block-structured.

<a id="lean-review-10"></a>

## Trace Example From This Workspace <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Show a historical Coq trace with unfinished local proofs. | substantial adaptation</span>

<span style="color:red"><strong>Why:</strong> The JSONL trace and .v output are historical Coq evidence. Translating code cannot turn them into Lean evidence.<br><strong>Proposed change:</strong> Retain them as history; collect a real Lean trace if a Lean teaching example is later added.</span>

The trace in <span style="color:gray">`2007-RTSS-Theorem3-opencode-github-copilot_gpt-5-4-20260418145414/opencode_events.jsonl`</span> repeatedly reached:

```text
File "./theorem.v", line 111, characters 2-25:
Error: Expected a single focused goal but 2 goals are focused.
```

The failing script shape was roughly:

<a id="lean-review-code-8"></a>

<span style="color:red"><strong>Purpose:</strong> Show a Coq trace that continues while nested local proofs are unfinished.<br><strong>Proposed Lean adaptation:</strong> A future Lean version would use nested have/by blocks and actual branch states. Keep this as historical evidence until an observed Lean trace supports the replacement.</span>

```coq
move=> j0 ARR0 JOB0.
apply/negP => NOTCOMP0.
have PENDING0 : forall t,
    a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t.
Proof.
  ...
Qed.
have SLOT_BOUND : forall t,
    a0 <= t < a0 + R ->
    1 <= backlogged job_arrival job_cost sched j0 t + service_at sched j0 t.
Proof.
  ...
  case E: (service_at sched j0 t) => [|k] /=.
  - ...
  - ...
Qed.
apply: leq_trans ...
```

Why this drifted:

<span style="color:red"><strong>Why:</strong> Ordinary Lean negation does not require the negP reflection entry point.<br><strong>Proposed change:</strong> Introduce the negated proposition directly; retain any necessary handling of actual Bool definitions.</span>

- <span style="color:gray">`apply/negP` changed the main goal into a reflected boolean goal</span>.
- `have PENDING0` opened a local proof.
- `have SLOT_BOUND` opened another local proof.

<span style="color:red"><strong>Why:</strong> Here Coq case creates branches, whereas Lean case selects one.<br><strong>Proposed change:</strong> Use <code>cases h : ...</code> and handle each generated branch.</span>

- Inside `SLOT_BOUND`, <span style="color:gray">`case E: ...`</span> split the proof again.
- Later tactics resumed as if only one goal were active, but at least one branch or local proof had not been structurally closed the way the script expected.

This is why the right repair is branch management, not another lemma.

What the repair protocol should conclude at this point:
- The main theorem is frozen.
- The only valid next move is to close the currently open local proof or branch.

- Any later lemma-application mismatch is diagnostic noise until the focus count returns to one.

<a id="lean-review-11"></a>

## Bullet-Based Repair Pattern <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Finish local facts in sequence before the main proof.</span>
Prefer this shape instead:

<a id="lean-review-code-9"></a>

<span style="color:red"><strong>Purpose:</strong> Prove the local facts in sequence, then sum their contributions over the interval.<br><strong>Proposed Lean adaptation:</strong> Keep the sequence of local proofs. Use actual RTS definitions, explicit Bool.toNat for numeric Bool contributions and the matching Lean interval sum; verify every business declaration.</span>

```coq
move=> j0 ARR0 JOB0.
apply/negP => NOTCOMP0.

have PENDING0 : forall t,
    a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t.
{
  move=> t /andP [GE LT].
  apply/andP; split.
  - by rewrite /has_arrived GE.
  - apply/negP => COMPt.
    apply/negP: NOTCOMP0.
    rewrite /completed in COMPt *.
    apply: leq_trans COMPt _.
    rewrite /service [in X in _ <= X](@big_cat_nat _ _ _ t) //=.
    by rewrite leq_addr.
}

have SLOT_BOUND : forall t,
    a0 <= t < a0 + R ->
    1 <= backlogged job_arrival job_cost sched j0 t + service_at sched j0 t.
{
  move=> t LT.
  have PEND := PENDING0 t LT.
  move: PEND => /andP [ARRIVED NOTCOMP].
  rewrite /backlogged /pending ARRIVED NOTCOMP /=.
  rewrite (not_scheduled_no_service (sched := sched) (j := j0)).
  case E: (service_at sched j0 t) => [|k] /=.
  - by rewrite eq_refl.
  - by rewrite add0n.
}

have TOTAL_GE_R :
    R <= total_interference job_arrival job_cost sched j0 a0 (a0 + R) +
         service_during sched j0 a0 (a0 + R).
{
  apply: leq_trans.
  - apply: leq_sum => t LT.
    exact: SLOT_BOUND t LT.
  - rewrite big_split /=.
    rewrite /total_interference /service_during.
    by rewrite big_const_nat iter_addn mul1n addn0 addKn.
}
```

Why this is safer:
- Each `have` is fully discharged inside braces.
- The outer theorem resumes only after the local proof returns to one focused outer goal.

<span style="color:red"><strong>Why:</strong> The repair uses Coq case syntax.<br><strong>Proposed change:</strong> Use Lean cases/by_cases and finish each local proof before continuing the outer proof.</span>

- The <span style="color:gray">`case`</span> split is handled immediately with bullets.
- The script never pretends a multi-goal state is still linear.

<a id="lean-review-12"></a>

## Minimal Debug Log <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Record the current goal, branch and preceding step.</span>
Keep a short log while editing.

```text
Current focused goal count:
Current active goal owner:
Previous tactic:
Did it open a branch or sublemma: yes/no
Current bullet level:
Need `{ ... }` around `have`: yes/no
Am I inside an unclosed local proof: yes/no
Is the next move a recovery step rather than a math step: yes/no
Next tactic is valid for one goal only: yes/no
Next split target literally appears in the goal head: yes/no
Need to unfold a wrapper definition before splitting: yes/no
Last closing hypothesis was explicitly consumed: yes/no
```

<a id="lean-review-13"></a>

## Success Condition <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Confirm that branch handling matches the intended proof.</span>

The proof is back on track when every branch-producing tactic is followed by bullets, every `have` proof is isolated in `{ ... }`, every split acts on a literal visible goal head rather than a hidden wrapper definition, and every branch-ending hypothesis is explicitly consumed before the script resumes the outer proof.
