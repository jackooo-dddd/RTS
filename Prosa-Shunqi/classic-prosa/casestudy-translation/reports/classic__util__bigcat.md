# Report: `classic/util/bigcat.v` (rank 13)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/bigcat.v` |
| sha256 | `b7f0caba7bec38b1971a99cebd0b07088868400186bde58a7d64cd8be6db011d` |
| Lean module | `Prosa/Classic/Util/Bigcat.lean` (namespace `Prosa.Classic.Util.Bigcat`) |
| Tier / layer | S / 3 |
| Status | **TRANSLATED**: compiles (Lean 4.33.1, pinned Mathlib), no `sorry`; `#print axioms` ⊆ {`propext`, `Quot.sound`, `Classical.choice`} |
| Validation | pending Stage 0 (classic pipeline extension) |

## Declarations (6 source → Lean, same names)

- `Lemma` `mem_bigcat_ord`
- `Lemma` `mem_bigcat_ord_exists`
- `Lemma` `bigcat_ord_uniq`
- `Lemma` `map_bigcat_ord`
- `Lemma` `size_bigcat_ord`
- `Lemma` `size_bigcat_ord_max`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Lemmas about big concatenation over ordinals.  The source re-exports
`prosa.util.bigcat` (imported above).

Representation notes: `'I_n` is `Fin n`; MathComp's `\cat_(i < n) f i`
(`\big[cat/nil]` over `'I_n` in increasing order) is
`((List.finRange n).map f).flatten`, the map-then-flatten form also used for the
v0.6 big-concatenation helpers; `\sum_(i < n) F i` over ordinals is Mathlib's
`∑ i : Fin n, F i`.

## History

- 2026-10-01: translated; build and axiom check passed.
