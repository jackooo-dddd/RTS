---
name: lean-count-bridging
description: 'Handle Lean 4 proof branches where the same quantity appears as an indicator sum (`if P x then 1 else 0`), a filtered sum or list length, a count (`List.countP`, `Finset.card` of a filter), and then a `min` bound or arithmetic inequality. Use when rewrites keep failing because the branch has no stable counting normal form.'
argument-hint: 'Describe the current indicator or count shape, the target equality or inequality, and the first failed rewrite or bridge step.'
user-invocable: true
---

# Lean Count Bridging

Connect equivalent ways of counting before proving a bound. Example: four tasks contribute 1, 0, 1, 0 to a sum, while the theorem you want to use counts the two unfinished tasks directly. Choose the form the theorem expects, connect the expressions, and only then prove the bound.

## When to Use
- A branch mixes `∑ … (if P x then 1 else 0)`, `List.filter`/`Finset.filter`, `List.countP`, `.length`, `Finset.card`, and `min`.
- The current term is an indicator sum, but the lemma you need is about a count (or the reverse).
- You are bounding how many elements satisfy a predicate and then feeding that bound into an inequality or a `min`.
- The same quantity is being rewritten back and forth between a filtered list, a filtered sum, and a count.

## Lists versus finite sets
Prosa usually works over **lists** (job sequences, task sets as `List`), where duplicates count. Keep list forms when multiplicities matter:
- Prosa: `sumSeq r F = (r.map F).sum`, `sumFiltered r P F = ((r.filter P).map F).sum` (in `Prosa.Util.Sum`); counts as `r.countP P` with a `Bool` predicate.
- Core/Mathlib lists: `List.countP`, `List.filter`, `List.length`, `List.sum`, `List.countP_eq_length_filter`.

Use `Finset` forms (`Finset.sum`, `(s.filter p).card`, `Finset.sum_boole`, `Finset.card_filter`) only when the objects really are a finite set (no duplicates), for example `Finset.range n` or `Finset.Ico t (t + Δ)` time intervals.

Do not convert a list to a `Finset` just to reach a lemma: the conversion drops duplicates and changes the count.

## Core Rule
Choose one counting normal form and move toward it monotonically:

1. indicator sum
2. filtered sum of ones / length of a filter
3. count (`countP` or `card` of a filter)
4. bound on the count, then `min` or final arithmetic

If the next lemma is about `countP`, normalize to `countP` first. If it is about sums, stay with the filtered sum. Do not oscillate.

## Required Procedure
1. Name the current shape (indicator sum, filtered sum, count, `min`/arithmetic layer) and its carrier (`List` or `Finset`).
2. Decide the target normal form from the lemma you will apply next (`#check` it).
3. Remove the indicator encoding first: state the connecting equality as a local `have` and prove it (often by `induction r` with `simp [List.countP_cons, …]`, or `Finset.sum_boole`/`Finset.card_filter` for finite sets).
4. Collapse a filtered sum of ones to a count (`List.countP_eq_length_filter`, or `simp` with the relevant `sum_map`/`length` lemmas; check each with `#check`).
5. Only then apply list-splitting, subset, or monotonicity lemmas (Prosa: `sub_count_seq` for pointwise implication, `count_predUI'` for two predicates).
6. Only after the count bound is stable, do the final arithmetic (`omega` with the count named via `set c := r.countP P with hc`).
7. Keep connector facts named and local: `have h_count : … = r.countP P := …`.

## Bool and Prop
Prosa predicates on jobs are often `Bool`-valued (`P : Job → Bool`), so filters and counts take `Bool` predicates and membership facts look like `P x = true`. Ordinary inequalities on `ℕ` are propositions; you do not need a Bool round trip for the arithmetic. Bridge only where a definition really is `Bool`: `decide`, `Bool.and_eq_true`, `beq_iff_eq`, `Nat.ble_eq` and `simp` lemmas convert between `= true` and the proposition.

## Canonical Bridge Order

```text
(r.map (fun x => if P x then 1 else 0)).sum
  -> ((r.filter P).map (fun _ => 1)).sum   or   (r.filter P).length
  -> r.countP P
  -> bound on r.countP P
  -> bound on min … / final arithmetic
```

Do not skip a bridge when the next lemma lives in a different layer.

## Bridge Templates

Indicator sum to count over a list (prove it by induction; do not leave `sorry`):

```lean
  have h_indicator_count :
      (r.map (fun x => if P x then 1 else 0)).sum = r.countP P := by
    induction r with
    | nil => simp
    | cons a r ih => cases h : P a <;> simp [List.countP_cons, h, ih] <;> omega
```

Finite-set version:

```lean
  have h_card : ∑ t ∈ Finset.range Δ, (if busy t then 1 else 0)
      = ((Finset.range Δ).filter busy).card := by
    rw [Finset.sum_boole]
```

(`Finset.sum_boole` may produce a cast; check the result in `lean_session` and finish with `simp`/`Nat.cast_id` if needed.)

Count to bound:

```lean
  have h_count_le : r.countP P ≤ r.countP Q :=
    sub_count_seq P Q r (fun x hx hPx => h_impl x hx hPx)
```

## Anti-Patterns
- Jumping from an indicator sum straight to a `min` inequality.
- Converting a list to a `Finset` (losing duplicates) to reach a lemma.
- Mixing `countP` and `filter … |>.length` in one branch without a named connecting equality.
- Running `omega` on goals that still contain sums or counts it treats as unrelated atoms; name them first.

## Success Condition
The branch reaches one count form with named connector facts, the count bound is proved on that form, and the final arithmetic step only sees named quantities.
