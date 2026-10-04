# Report: `classic/util/minmax.v` (rank 19)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/minmax.v` |
| sha256 | `48e90e800693897a4875bb71b6c6f937b12d3da41a8a427a65eb102072d4e0cf` |
| Lean module | `Prosa/Classic/Util/Minmax.lean` (namespace `Prosa.Classic.Util.Minmax`) |
| Tier / layer | S / 4 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (44 source → Lean, same names)

- `Fixpoint` `seq_argmin`
- `Fixpoint` `seq_argmax`
- `Lemma` `seq_argmin_exists`
- `Lemma` `seq_argmin_in_seq`
- `Lemma` `seq_argmax_exists`
- `Lemma` `seq_argmax_in_seq`
- `Lemma` `seq_argmin_computes_min`
- `Lemma` `seq_argmax_computes_max`
- `Definition` `seq_min`
- `Definition` `seq_max`
- `Lemma` `seq_min_exists`
- `Lemma` `seq_min_in_seq`
- `Lemma` `seq_max_exists`
- `Lemma` `seq_max_in_seq`
- `Lemma` `seq_min_computes_min`
- `Lemma` `seq_max_computes_max`
- `Definition` `seq_argmin_nat`
- `Definition` `seq_argmax_nat`
- `Lemma` `seq_argmin_nat_exists`
- `Lemma` `seq_argmin_nat_in_seq`
- `Lemma` `seq_argmax_nat_exists`
- `Lemma` `seq_argmax_nat_in_seq`
- `Lemma` `seq_argmin_nat_computes_min`
- `Lemma` `seq_argmax_nat_computes_max`
- `Definition` `seq_min_nat`
- `Definition` `seq_max_nat`
- `Lemma` `seq_min_nat_exists`
- `Lemma` `seq_min_nat_in_seq`
- `Lemma` `seq_max_nat_exists`
- `Lemma` `seq_max_nat_in_seq`
- `Lemma` `seq_min_nat_computes_min`
- `Lemma` `seq_max_nat_computes_max`
- `Definition` `values_between`
- `Lemma` `mem_values_between`
- `Definition` `min_nat_cond`
- `Definition` `max_nat_cond`
- `Lemma` `min_nat_cond_exists`
- `Lemma` `min_nat_cond_in_seq`
- `Lemma` `min_nat_cond_computes_min`
- `Lemma` `max_nat_cond_exists`
- `Lemma` `max_nat_cond_in_seq`
- `Lemma` `max_nat_cond_computes_max`
- `Fixpoint` `seq_argmin_k`
- `Lemma` `seq_argmin_k_exists`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `seq_argmin_ne_none`, `seq_argmax_ne_none`, `leq_trans'`, `leq_total'`, `mem_filter_values_between`.

## Representation notes

Minima and maxima of sequences (arg-min/arg-max with respect to a Boolean relation).

Representation notes:
* `seq T` is `List T`, `option T` is `Option T`; `Context {T1 T2 : eqType}` gives carriers
  with `[DecidableEq _]`; a relation `rel T` is `T → T → Bool`.
* `x \in l` in proposition position is `x ∈ l`; a Boolean equation
  `(x \in l) = (a <= x < b)` is `decide (x ∈ l) = (decide (a ≤ x) && decide (x < b))`;
  `s != None` in proposition position is `(!decide (s = none)) = true`; Boolean
  statements in proposition position are `… = true`.
* MathComp's `transitive R` is unfolded with its binder order
  (`∀ y x z, R x y = true → R y z = true → R x z = true`).
* `leq` as a relation is `fun x y => decide (x ≤ y)`; `id` is the identity function.
* `values_between a b` filters `map nat_of_ord (enum 'I_b)`, i.e.
  `(List.finRange b).map Fin.val`.
* `rem x s` (remove the first occurrence) is `List.erase s x`.
* The source re-exports the official v0.6 `util/minmax.v`, mirrored by the `export` of
  the accepted `Prosa.Util.Minmax` below.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
