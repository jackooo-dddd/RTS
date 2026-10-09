---
name: goal-focus-discipline
description: 'Handle Lean 4 proof-state drift: check which goals are open after every tactic that can split or close goals, focus branches with `·` / `case` / `next`, and finish each local `have` inside its own `by` block before returning to the main line.'
argument-hint: 'Describe the current goals, the previous tactic, and the branch or local `have` that introduced the drift.'
user-invocable: true
---

# Goal Focus Discipline

## When to Use
- Lean reports `unsolved goals` (often listing several cases) or `no goals to be proved` where the script expected a goal.
- A focusing dot `·` or `case tag =>` errors, or a tactic runs on a different goal than intended.
- A proof used to have one main line, then `constructor`, `refine ⟨?_, ?_⟩`, `rcases`, `cases`, `by_cases`, `induction`, or `apply` with side goals was added and later tactics stopped fitting.
- A local fact such as `h_pending` is introduced with `have`, and later tactics behave as if the main goal were the only goal.
- A branch "looks done" because its last line rewrote a hypothesis (`rw [...] at h`), but the branch goal was never closed.

## Core Rule
Do not choose the next tactic from proof intent alone. First look at the open goals (`lean_session` goal state, or the `unsolved goals` message) and at what the previous tactic created or closed.

- In Lean, tactics act on the **main goal** (the first one); the others wait. When a tactic creates several goals, focus each with `·` (or `case tag =>` / `next =>`) and finish it completely before the next.
- A `have h : P := by …` proves `P` in its own indented block; the outer proof resumes only when that block has no goals left.
- `apply lemma` can leave side goals for premises that were not unified; `refine lemma ?_ ?_` names them explicitly. Check how many goals came back.
- When the visible script layout and the live goal state disagree, trust the goal state.

Messages such as `unknown identifier 'h'` (a hypothesis introduced in another branch), `no goals to be proved`, or a type mismatch against the wrong goal are often secondary effects of focus drift. Repair the focus first.

## Required Procedure
1. Read the current goals before the next step: their number, their case tags, and the target of the main goal.
2. Inspect the previous tactic: did it split the proof, create side goals, introduce a local subgoal, or close a goal?
3. Inspect the literal goal head before a case split. If the term you want to split on is hidden under a definition (`job_misses_no_deadline j`), `unfold`/`simp only [def]` or `show` the unfolded form first; otherwise `by_cases`/`cases` splits on something the goal does not mention.
4. If the goals changed, respond structurally:
   - new branches: one `·` per goal (or `case tag =>`), at one indentation level;
   - local lemma: finish the `have`'s `by` block, then return;
   - closed branch: check that the next goal is the one you intend to work on.
5. When a branch seems finished, check that its last line actually closed the branch goal. Rewriting inside a hypothesis does not: finish with `exact h`, `exact absurd h hn`, `omega`, or `exact (h.trans …)`.
6. Only after the focus is right, choose the next rewriting or reasoning step.
7. Do not add bridge lemmas or helper facts to work around a focus problem.

Several open goals are not an error in themselves (Lean allows `all_goals`, `<;>`, `any_goals`), but each goal must be closed somewhere you can name.

## Hidden Goal Head Before Case Split

Pattern: the goal is `job_misses_no_deadline j`; the script does `by_cases h : completed sched j (job_arrival j + job_deadline j)` and expects the goal to change. It does not: the goal still mentions only the wrapper.

Repair: expose the head first.

```lean
  unfold job_misses_no_deadline
  by_cases h_done : completed sched j (job_arrival j + job_deadline j)
  · exact absurd h_done ‹_›
  · …
```

## Explicit Branch Closure

Bad: the branch ends with a rewrite of a hypothesis.

```lean
  · have h_lt : x < n + 1 := by omega
    rw [Nat.lt_succ_iff] at h_lt      -- the branch goal is still open
```

Good: consume the fact.

```lean
  · have h_lt : x < n + 1 := by omega
    exact Nat.lt_succ_iff.mp h_lt
```

For a contradiction branch, close it explicitly: `exact absurd h_le h_not_le`, `exact (h_ne rfl).elim`, or `omega` when the contradiction is arithmetic.

## Focusing Patterns

```lean
  constructor
  · -- left conjunct
    exact h_left
  · -- right conjunct
    have h_aux : a ≤ b := by
      exact le_trans h1 h2
    exact h_aux.trans h3

  rcases h with ⟨x, hx_mem, hx_eq⟩ | h_none
  · …        -- case with a witness
  · …        -- other case

  induction n with
  | zero => simp
  | succ k ih => …
```

## Anti-Patterns
- Writing linear tactics after a tactic created several goals.
- Patching a focus problem by introducing another helper lemma.
- Starting a `have` and continuing the outer script before its `by` block is finished (wrong indentation does this silently).
- Splitting on a term hidden under a definition.
- Ending a branch with `rw [...] at h` and assuming the branch is closed.
- Treating `unsolved goals` as a syntax error; it is a proof-structure error.
- Trusting the text layout over the live goal state.
- Repairing secondary errors (`unknown identifier`, a mismatch against the wrong goal) before the focus is fixed.

## Minimal Debug Log
When a focus problem is suspected, write down:
1. the previous tactic;
2. the goals now open (number and case tags);
3. which goal the next tactic is meant for;
4. which local `have` blocks are still open.

## Success Condition
Each branch is focused with `·`/`case`, each local `have` is closed inside its block, and the next tactic runs on the goal you can name.
