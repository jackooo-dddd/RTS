# Report: `classic/util/notation.v` (rank 4)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/notation.v` |
| sha256 | `6627a5c91214c8d7887f60021ed015ef3e62b80b31dbe8ca0d39ccdaea102a76` |
| Lean module | `Prosa/Classic/Util/Notation.lean` (namespace `Prosa.Classic.Util.Notation`) |
| Tier / layer | S / 1 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (6 source → Lean, same names)

- `Definition` `pair_1st`
- `Definition` `pair_2nd`
- `Definition` `triple_1st`
- `Definition` `triple_2nd`
- `Definition` `triple_3rd`
- `Definition` `make_sequence`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

The source re-exports `prosa.util.notation` (imported above), defines pair and
triple projections and an option-to-list wrapper, and declares notations for
big sums/maxima over lists of pairs, pair filters/maps and membership in an
optional list.  The notations become `LEAN_HELPER` definitions with the same
meaning: MathComp's `\sum_(i <- r) F` is `List.sum (r.map F)` (a right fold with
`+` and `0`), and `\max_(i <- r) F` is the right fold of `maxn` from `0`.

Representation note: Rocq's `A * B * C` is `(A * B) * C`; Lean's `×` associates
to the right, so triples are written `(A × B) × C`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: accepted.
