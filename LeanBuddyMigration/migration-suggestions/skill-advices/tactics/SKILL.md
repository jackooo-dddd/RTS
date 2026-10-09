<span style="color:red"><strong>Purpose:</strong> Diagnose a compact SSReflect proof by removing its by closing wrapper, running the inner tactics and inspecting the first exposed failure.</span>

<span style="color:red"><strong>Proposed removal of the entire skill from the future Lean version:</strong> SSReflect by runs tactics and attempts to close their goals; Lean by introduces a tactic proof block. Removing Lean by can make the proof syntactically invalid, so this skill's central action does not transfer. General step-by-step inspection can remain in guide, with Lean by kept intact.</span>

<span style="color:red"><strong>Review only:</strong> The full original skill and all examples below are retained. No deletion or Lean rewrite has been applied.</span>

---
name: by-expansion-diagnostics
#<span style="color:red"><strong>description recommendation:</strong> No replacement description is proposed: recommend removing this whole skill from the future Lean version. Reason: its remove-by procedure is specific to SSReflect.</span>
description: 'Debug Coq and ssreflect `No applicable tactic` failures that arise on `by ...` lines by removing `by`, exposing the remaining goals, and treating the first revealed proof state as the real error signal. Use when a compact `by rewrite`, `by apply:`, `have ... by ...`, or `case ...; by ...` script hides whether the failure is a rewrite mismatch, a missing assumption, or an unexpected branch split.'
#<span style="color:red"><strong>argument-hint recommendation:</strong> No new hint is needed if the proposed removal is adopted. The original hint is retained for this review.</span>
argument-hint: 'Describe the failing `by ...` line, the current goal, and the first message after expanding it.'
user-invocable: true
---

# By Expansion Diagnostics <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Expose failures hidden by SSReflect compact closure; proposed removal for Lean.</span>

<a id="lean-review-1"></a>

## When to Use <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Recognize SSReflect compact-proof failures.</span>

- <span style="color:gray">Coq reports `No applicable tactic` on a line that starts with `by` or ends in a compressed `...; by ...` tail.</span>
- A large model reacts to the flat error by trying random rewrites or lemma applications.
- You do not know whether the real failure is a rewrite mismatch, a missing assumption, or an extra branch.

- The failing line is a short script such as <span style="color:gray">`by rewrite ...`</span>, <span style="color:gray">`by apply: ...`</span>, <span style="color:gray">`have H : P by ...`</span>, or <span style="color:gray">`case E: x; by ...`</span>.

<a id="lean-review-2"></a>

## Core Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Remove the SSReflect closing wrapper to inspect its inner step.</span>

<span style="color:gray">Treat `by` as a proof-state compressor, not as a diagnostic tactic.</span>

When `by ...` fails, do not immediately try other tactics.

<span style="color:gray">Remove `by`, rerun the exact payload</span>, and inspect the first revealed proof state. That first revealed state is the real debugging signal.

<a id="lean-review-3"></a>

## Why `by` Hides the Useful Error <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Explain how SSReflect by adds an automatic closing attempt.</span>

<span style="color:gray">`by tac.` means: run `tac` and close every resulting goal immediately.</span>

If `tac` does any of the following,
- leaves one goal unsolved,
- opens two or more goals,
- rewrites the wrong normal form,
- applies a lemma with mismatched premises,

then <span style="color:gray">Coq often reports only `No applicable tactic` at the compressed line</span>.

After expansion, the hidden signal usually becomes one of these:
- a concrete remaining goal,

- <span style="color:gray">`Expected a single focused goal but 2 goals are focused.`</span>,
- <span style="color:gray">`The LHS of ... does not match any subterm of the goal.`</span>,
- <span style="color:gray">`Cannot apply lemma ...`</span>,
- <span style="color:gray">`No assumption in ...`</span>.

That specific message is what you should debug, not <span style="color:gray">the original flat `by` failure</span>.

<a id="lean-review-4"></a>

## Required Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Expand the compact proof and inspect the first exposed failure.</span>
1. Freeze the exact failing line.
   - Copy the `by ...` line exactly.
   - Do not rewrite its payload yet.
2. Expand only that one compression boundary.

   - <span style="color:gray">Remove `by`.</span>
   - Keep the original tactic payload unchanged.
3. Re-run immediately.
   - Record the first new message.
   - Record the number of focused goals.
4. Classify the revealed signal.
   - One remaining goal: the compressed script was incomplete.

   - More than one goal: the payload split the proof and needs bullets or braces.
   - Rewrite mismatch: the current goal shape does not match the intended lemma.

   - Apply or intro mismatch: the theorem head, premises, or <span style="color:gray">view pattern</span> is wrong.
5. Only then choose the next repair.

   - If branches appeared, fix proof structure first.
   - If a rewrite mismatch appeared, debug the exact goal syntax.
   - If a premise mismatch appeared, inspect the theorem application.

6. <span style="color:gray">Re-compress back to `by`</span> only after the expanded script actually closes all goals.

## Expansion Templates <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Show common SSReflect expansion patterns.</span>

### Plain `by rewrite` <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Expand a compact rewrite.</span>
Original:

<a id="lean-review-code-1"></a>

```coq
by rewrite L1 L2 L3.
```

Expand to:

<a id="lean-review-code-2"></a>

```coq
rewrite L1 L2 L3.
```

Do not change the rewrite list until you see which exact rewrite fails or what goal remains.

### Plain `by apply:` <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Expand a compact theorem application.</span>
Original:

<a id="lean-review-code-3"></a>

```coq
by apply: some_lemma.
```

Expand to:

<a id="lean-review-code-4"></a>

```coq
apply: some_lemma.
```

Now inspect whether <span style="color:gray">Coq</span> exposed missing premises, extra subgoals, or an application mismatch.

### `have ... by ...` <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Separate a local fact from its compact proof.</span>
Original:

<a id="lean-review-code-5"></a>

```coq
have H : P by tac.
```

Expand to:

<a id="lean-review-code-6"></a>

```coq
have H : P.
{
  tac.
}
```

This isolates the local proof and prevents drift into the outer proof.

### `suff ... by ...` <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Separate a sufficient condition from its compact proof.</span>
Original:

<a id="lean-review-code-7"></a>

```coq
suff H : P by tac.
```

Expand to:

<a id="lean-review-code-8"></a>

```coq
suff H : P.
- tac.
```

Then inspect the newly exposed sufficiency goal separately.

### `case ...; by ...` <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Inspect each branch of a compact case split.</span>
Original:

<a id="lean-review-code-9"></a>

```coq
case E: x; by tac.
```

Expand to:

<a id="lean-review-code-10"></a>

```coq
case E: x.
- tac.
- tac.
```

If the branches are not symmetric, the expansion will show which branch actually needs a different proof.

<a id="lean-review-5"></a>

## First Revealed Error -> Real Cause <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Relate the exposed failure to the next check.</span>

- <span style="color:gray">`Expected a single focused goal but 2 goals are focused.`</span>
  The payload opened branches. This is a structure problem, not a math problem.

- <span style="color:gray">`The LHS of ... does not match any subterm of the goal.`</span>
  The chosen rewrite does not literally fit the current goal shape.

- <span style="color:gray">`Cannot apply lemma ...`</span>
  The theorem head or expected premise shape is wrong.

- <span style="color:gray">`No assumption in ...`</span>
  An <span style="color:gray">intro pattern, view pattern, or moved hypothesis</span> does not exist in the current context.
- A concrete goal remains with no special error.

  <span style="color:gray">The original `by` was simply too optimistic.</span> Read and solve that goal directly.

## Examples <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Show historical compact-proof failures.</span>

### Example 1: `by` Hides a Rewrite Mismatch <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Expose a rewrite mismatch.</span>
Compressed script:

<a id="lean-review-code-11"></a>

```coq
by rewrite big_const_ord iter_addn mul1n.
```

Expand to:

<a id="lean-review-code-12"></a>

```coq
rewrite big_const_ord iter_addn mul1n.
```

What this often reveals:

- <span style="color:gray">`mul1n` does not match because the goal is still in `iter` form</span>.
- Or the multiplication appears as `n * x`, not `1 * x`.

Correct reaction:
- Stop guessing.

- Read the exact intermediate goal after <span style="color:gray">`big_const_ord`</span> and <span style="color:gray">`iter_addn`</span>.
- Decide whether you need a bridge lemma or a different arithmetic normal form.

### Example 2: `by apply:` Hides Missing Premises <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Expose missing theorem premises.</span>
Compressed script:

<a id="lean-review-code-13"></a>

```coq
by apply: leq_trans.
```

Expand to:

<a id="lean-review-code-14"></a>

```coq
apply: leq_trans.
```

What this often reveals:
- two ordinary comparison goals,
- or a missing middle bound that was never named.

Correct reaction:
- Prove or name the intermediate inequality.
- Do not swap in a different lemma until you read the actual subgoals.

### Example 3: `have ... by ...` Hides an Incomplete Local Proof <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Expose an unfinished local proof.</span>
Compressed script:

<a id="lean-review-code-15"></a>

```coq
have PENDING0 : forall t, a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t by
  move=> t /andP [GE LT]; apply/andP; split.
```

Expand to:

<a id="lean-review-code-16"></a>

```coq
have PENDING0 : forall t, a0 <= t < a0 + R -> pending job_arrival job_cost sched j0 t.
{
  move=> t /andP [GE LT].
  apply/andP; split.
}
```

What this reveals:
- the first conjunct may be solved,
- the second conjunct still needs a backlog or completion argument.

Correct reaction:
- Finish the exposed second conjunct.
- Do not invent a new helper lemma before reading that exact missing goal.

### Example 4: `case ...; by ...` Hides Branch Asymmetry <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Expose branches requiring different arguments.</span>
Compressed script:

<a id="lean-review-code-17"></a>

```coq
case E: (service_at sched j0 t) => [|k] /=; by rewrite add0n.
```

Expand to:

<a id="lean-review-code-18"></a>

```coq
case E: (service_at sched j0 t) => [|k] /=.
- rewrite add0n.
- rewrite add0n.
```

What this reveals:
- the zero branch may close,
- the successor branch may need a different argument entirely,

- or <span style="color:gray">Coq may complain about multiple focused goals if bullets were missing</span>.

Correct reaction:
- manage the branches explicitly,
- then solve each branch from its own goal shape.

<a id="lean-review-6"></a>

## What To Do After Expansion <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Choose a repair from the revealed proof state.</span>

- If expansion reveals multiple goals, switch to the goal-count and bullet discipline in `skill_goal.md`.

- If expansion reveals a rewrite mismatch, debug the literal goal shape as in `.github/skills/coq-proof-state-discipline/skill_math.md`.
- If expansion reveals theorem-application ambiguity before ordinary goals appear, switch to early-bound argument diagnosis instead of adding random premises.

<a id="lean-review-7"></a>

## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Avoid hiding failures under further compact tactics.</span>
- Do not respond to a failing `by` by trying three other rewrite lists first.

- Do not <span style="color:gray">remove `by`</span> and simultaneously change the tactic payload. Expand first, then inspect.
- Do not expand the whole proof at once. Expand one compression boundary at a time.

- Do not leave <span style="color:gray">`have H : P.`</span> floating inline when its local proof can drift. Use braces.

- Do not <span style="color:gray">compress back to `by`</span> until the expanded form is known to close every resulting goal.

<a id="lean-review-8"></a>

## Minimal Debug Log <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Record the compact command and the revealed failure.</span>

```text
Failing compact line:
Expanded form:
First revealed message:
Focused goal count after expansion:
Did the payload split goals: yes/no
Real problem class: rewrite mismatch / missing premise / extra branch / incomplete local proof
Next repair chosen from revealed signal:
```

<a id="lean-review-9"></a>

## Success Condition <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Confirm that the underlying failure has been identified.</span>

This skill has worked when the flat <span style="color:gray">`No applicable tactic`</span> has been replaced by a specific, local proof-state diagnosis, and the next tactic is chosen from that diagnosis instead of from blind trial and error.

If the expanded form closes the proof cleanly, then and only then is it reasonable to <span style="color:gray">compress it back into `by`</span>.
