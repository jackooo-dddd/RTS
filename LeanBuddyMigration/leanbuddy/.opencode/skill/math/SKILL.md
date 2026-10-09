---
name: lean-rewrite-discipline
description: 'Debug Lean 4 proofs by following the exact goal: choose a rewrite only when its left-hand side occurs in the goal (up to instances), and add a small connecting equality when sums, products, casts or `if`-indicators are in a different form. Use when `rw` reports that it did not find the pattern or that the motive is not type correct, when `simp` makes no progress, or when a step is mathematically obvious but Lean rejects it.'
argument-hint: 'Describe the goal, the failed rewrite or tactic, and the current goal shape.'
user-invocable: true
---

# Lean Rewrite Discipline

## When to Use
- A rewrite should work mathematically, but `rw` reports `did not find instance of the pattern in the target expression`.
- `rw` fails with `motive is not type correct` (the term occurs inside a dependent type or under a binder).
- `simp only [...]` makes no progress, or `simp` rewrites into a form you did not expect.
- A proof oscillates between `∑ i ∈ s, f i`, `s.card • c`, `c * s.card`, and `if … then 1 else 0` forms.
- `linarith`/`omega` fail although the inequality is "obvious": the terms are not in the form the tactic sees (casts, `min`, `-` on `ℕ`, a function application it treats as an atom).

## Core Rule
Choose the next lemma from the exact current goal, not from mathematical intent alone. Before rewriting, write down the lemma's left-hand side (`#check @lemma`) and find it in the goal. If it is not there, first normalize one side or state a connecting equality.

`rw` matches syntactically (up to reducible unfolding and instances) and cannot rewrite under binders (inside `∑ i ∈ s, …`, `∀`, `fun`). For those, use `simp only [lemma]`, `Finset.sum_congr rfl (fun i hi => …)`, or `conv`.

## Procedure
1. Quote the goal or the smallest relevant subterm (`lean_session` goal state).
2. Name the intended rewrite and its exact left-hand side (`lean_query #check @Finset.sum_const`).
3. Check that the left-hand side occurs in the goal, with the same implicit arguments (the same `Finset`, the same function, the same coercion).
4. If not, add the smallest bridge:
   - a local `have h : lhs_in_goal = form_you_need := by …` and `rw [h]`;
   - `show` the goal in the unfolded form you need (it must be definitionally equal);
   - `simp only [def]` / `unfold def` to expose a definition.
5. Normalize inside-out: settle inner sums and indicators first, then distribute or factor outer sums; commute products only after the multiplication is literally there.
6. Re-read the goal after each nontrivial rewrite. If its head form changed, update the plan.
7. Keep one stable normal form per branch; do not alternate between `s.card • c`, `c * s.card` and `s.card * c`.

## Connecting Equalities

Prefer a local bridge when it depends on fixed local data:

```lean
  have h_cpu_sum : ∑ _cpu ∈ Finset.range num_cpus, (if backlogged sched j t then 1 else 0)
      = (if backlogged sched j t then 1 else 0) * num_cpus := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
```

Useful Mathlib facts (check each with `#check` before use; names and argument order matter):
- `Finset.sum_const : ∑ _x ∈ s, c = s.card • c`, then `smul_eq_mul`;
- `Finset.card_range : (Finset.range n).card = n`;
- `Finset.sum_mul`, `Finset.mul_sum` (pull a constant factor out of a sum);
- `Finset.sum_comm` (swap two sums), `Finset.sum_add_distrib`;
- `Finset.sum_boole : ∑ i ∈ s, (if p i then 1 else 0) = (s.filter p).card` (see `lean-count-bridging` for counting proofs);
- `Finset.sum_le_sum` (pointwise bound), `Finset.sum_congr rfl` (pointwise equality under the binder).

Prosa has its own sum and count helpers (for example in `Prosa.Util.Sum`); search them with `lean_query search` and prefer them when the goal is stated with Prosa definitions.

## Arithmetic Endgame
- `omega` works on `ℕ`/`ℤ` linear arithmetic with `+`, `-` (truncated on `ℕ`), `*` by constants, `/`, `%`, `min`, `max`; it treats other terms (function applications, sums) as atoms, so name them first (`set S := ∑ … with hS`).
- `linarith` needs the relevant facts as hypotheses or arguments (`linarith [h1, h2]`); it does not unfold definitions.
- Truncated subtraction on `ℕ`: `a - b + b = a` needs `b ≤ a` (`Nat.sub_add_cancel`); `omega` handles it when the side condition is in context.
- Casts: move to one type first (`push_cast`, `Nat.cast_le`, `exact_mod_cast`).

## When To Switch To Count Bridging
If the branch mixes `if … then 1 else 0` sums, `filter`/`countP`/`card`, and a `min` or a bound on how many elements satisfy a predicate, switch to `lean-count-bridging`: that is a counting-normalization proof, not a generic rewrite mismatch.

## Anti-Patterns
- Rewriting because two expressions are mathematically equal when the lemma's left-hand side is not in the goal.
- Chaining `rw [a, b, c, d]` blindly without checking the intermediate goals.
- Using a bare `simp` that also rewrites parts you rely on later; prefer `simp only [...]`.
- Switching normal forms repeatedly inside one branch.

## Minimal Debug Log

```text
Current goal subterm:
Desired lemma and its left-hand side (#check):
Occurs in goal (same implicit arguments): yes/no
If no, bridge step:
Resulting goal head form:
```

## Success Condition
Each rewrite's left-hand side was found in the goal before it was applied, each branch keeps one normal form, and the final arithmetic step sees the terms in a form it handles.
