# Report: `classic/util/bigord.v` (rank 7)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/bigord.v` |
| sha256 | `5f7b93e97c6c71e8b22cec68c54f0a80b3e4952c78e287cb14e409ad773fef67` |
| Lean module | `Prosa/Classic/Util/Bigord.lean` (namespace `Prosa.Classic.Util.Bigord`) |
| Tier / layer | S / 2 |
| Status | **TRANSLATED**: compiles (Lean 4.33.1, pinned Mathlib), no `sorry`; `#print axioms` ⊆ {`propext`, `Quot.sound`, `Classical.choice`} |
| Validation | pending Stage 0 (classic pipeline extension) |

## Declarations (4 source → Lean, same names)

- `Definition` `fun_ord_to_nat`
- `Lemma` `eq_fun_ord_to_nat`
- `Lemma` `eq_bigr_ord`
- `Lemma` `big_mkord_ord`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Lemmas about big operators over ordinals.

Representation notes:
* `'I_n` is `Fin n`; `Ordinal LT` is `⟨x, LT⟩`; the coercion to `nat` is `.val`.
* The generic big operator `\big[op/idx]_(i <- r | P i) F i` (no monoid laws) is the
  accepted v0.6 right fold `Prosa.Util.Bigop.bigSeq idx op P F r`, and
  `\big[op/idx]_(i < n | P i) F i` ranges over `'I_n` in increasing order, i.e.
  over `List.finRange n`.

## History

- 2026-10-01: translated; build and axiom check passed.
