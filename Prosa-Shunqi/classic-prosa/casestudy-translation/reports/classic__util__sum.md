# Report: `classic/util/sum.v` (rank 20)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/sum.v` |
| sha256 | `6ed53c42fe02f421299fdfd603b17e5ebf18bcc913c01bc673ea36f5f51c7c95` |
| Lean module | `Prosa/Classic/Util/Sum.lean` (namespace `Prosa.Classic.Util.Sum`) |
| Tier / layer | S / 4 |
| Status | **TRANSLATED**: compiles (Lean 4.33.1, pinned Mathlib), no `sorry`; `#print axioms` ⊆ {`propext`, `Quot.sound`, `Classical.choice`} |
| Validation | pending Stage 0 (classic pipeline extension) |

## Declarations (9 source → Lean, same names)

- `Lemma` `sum_seq_diff`
- `Lemma` `sum_diff`
- `Lemma` `extend_sum`
- `Lemma` `leq_sum_nat`
- `Lemma` `leq_sum1_smaller_range`
- `Lemma` `leq_pred_sum`
- `Lemma` `sum_le_summation_range`
- `Lemma` `telescoping_sum`
- `Lemma` `leq_sum_sub_uniq`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Lemmas about sums.  The source re-exports `prosa.util.sum` (imported above) and
the Ltac-only `prosa.classic.util.ssromega` (no Lean counterpart; Lean proofs use
`omega`).

Representation notes (as in the accepted v0.6 translation):
* `\sum_(i <- r) F i` is `Prosa.Util.Sum.sumSeq r F` and
  `\sum_(i <- r | P i) F i` is `Prosa.Util.Sum.sumFiltered r P F`;
* `\sum_(m <= i < n) F i` is `∑ i ∈ Finset.Ico m n, F i`, and
  `\sum_(m <= i < n | P i) F i` is `∑ i ∈ (Finset.Ico m n).filter (P · = true), F i`;
* `m <= i < n` in proposition position is `m ≤ i ∧ i < n`; `nth x0 r i` is
  `r.getD i x0`; `{subset r1 <= r2}` is `∀ x, x ∈ r1 → x ∈ r2`.

## History

- 2026-10-01: translated; build and axiom check passed.
