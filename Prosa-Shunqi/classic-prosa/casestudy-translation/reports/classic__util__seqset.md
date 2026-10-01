# Report: `classic/util/seqset.v` (rank 5)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/seqset.v` |
| sha256 | `609b66c1b2b9d5c5aaa3937f98789f8898a33fe36fca3b67a72849af8c2b03cb` |
| Lean module | `Prosa/Classic/Util/Seqset.lean` (namespace `Prosa.Classic.Util.Seqset`) |
| Tier / layer | S / 1 |
| Status | **TRANSLATED**: compiles (Lean 4.33.1, pinned Mathlib), no `sorry`; `#print axioms` ⊆ {`propext`, `Quot.sound`, `Classical.choice`} |
| Validation | pending Stage 0 (classic pipeline extension) |

## Declarations (2 source → Lean, same names)

- `Lemma` `set_mem`
- `Lemma` `set_card`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `memDecidable`.

## Representation notes

The source re-exports `prosa.util.seqset` (imported above: the accepted v0.6
sequence-set `Prosa.Util.Seqset.set`) and proves two facts.

Representation notes:
* Boolean membership equalities `(x \in a) = (x \in b)` are written
  `decide (x ∈ a) = decide (x ∈ b)`, as in the accepted v0.6 translation.
* `Context {T : finType}` is a carrier with `[Fintype T] [DecidableEq T]`
  (v0.6 `finType` policy); MathComp's `#|s|` is the number of elements of `T`
  in `s`, i.e. `(Finset.univ.filter (· ∈ s)).card`.

## History

- 2026-10-01: translated; build and axiom check passed.
