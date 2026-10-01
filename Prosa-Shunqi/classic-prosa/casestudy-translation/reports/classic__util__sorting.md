# Report: `classic/util/sorting.v` (rank 17)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/sorting.v` |
| sha256 | `707c3ef0d575628941cff76b26368383a0f21fd3f85082fbd1f4b42593a94d58` |
| Lean module | `Prosa/Classic/Util/Sorting.lean` (namespace `Prosa.Classic.Util.Sorting`) |
| Tier / layer | S / 3 |
| Status | **TRANSLATED**: compiles (Lean 4.33.1, pinned Mathlib), no `sorry`; `#print axioms` ⊆ {`propext`, `Quot.sound`, `Classical.choice`} |
| Validation | pending Stage 0 (classic pipeline extension) |

## Declarations (6 source → Lean, same names)

- `Lemma` `sort_ordered`
- `Lemma` `sorted_rcons_prefix`
- `Lemma` `order_sorted_rcons`
- `Lemma` `sorted_lt_idx_implies_rel`
- `Lemma` `sorted_rel_implies_le_idx`
- `Lemma` `prev_le_next`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `getD_lt`, `chain_rel_of_lt`.

## Representation notes

Lemmas about sorted sequences.

Representation notes:
* MathComp's `sorted leT xs` relates adjacent elements; as in the accepted v0.6
  translation it is `List.IsChain (fun a b => leT a b = true) xs`.
* `rel T` is `T → T → Bool`; `transitive leT` is MathComp's
  `∀ y x z, leT x y → leT y z → leT x z`, kept with the same binder order.
* The section variables `T`, `leT`, `xs`, `default` and the transitivity
  hypothesis become leading arguments in declaration order, only where used
  (as Rocq abstracts them when the section is closed).
* The section-local `nth := nth default` is `List.getD · · default`;
  `(size xs).-1` is `xs.length - 1`.
* `def` is a Lean keyword, so the source binder `def` is written `«def»`.

## History

- 2026-10-01: translated; build and axiom check passed.
