# Report: `classic/util/nat.v` (rank 10)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/nat.v` |
| sha256 | `2b58a32d71e0036ae81f0d3cc251ed8125df8fd4c9bbfa1889878da737321b52` |
| Lean module | `Prosa/Classic/Util/Nat.lean` (namespace `Prosa.Classic.Util.Nat`) |
| Tier / layer | S / 2 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (8 source → Lean, same names)

- `Lemma` `subh1`
- `Lemma` `subh2`
- `Lemma` `addnb`
- `Lemma` `subh4`
- `Lemma` `addmovr`
- `Lemma` `addmovl`
- `Lemma` `ltSnm`
- `Lemma` `min_lt_same`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Additional lemmas about natural numbers.  The source re-exports
`prosa.util.nat` (imported above).

Representation notes: Boolean equalities `(a == b)` in a Boolean equation are
`decide (a = b)`; `a != b` is `!decide (a = b)`; the `bool → nat` coercion is
`Bool.toNat`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
