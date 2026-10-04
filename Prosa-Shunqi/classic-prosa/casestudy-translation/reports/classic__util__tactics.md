# Report: `classic/util/tactics.v` (rank 6)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/tactics.v` |
| sha256 | `ef510807df731b2b41e1a8c30f9af1e99916d54ec2f72b0829044757c68147ae` |
| Lean module | `Prosa/Classic/Util/Tactics.lean` (namespace `Prosa.Classic.Util.Tactics`) |
| Tier / layer | S / 1 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (13 source → Lean, same names)

- `Lemma` `vlib__internal_eqP`
- `Lemma` `beq_refl`
- `Lemma` `beq_sym`
- `Lemma` `vlib__negb_rewrite`
- `Lemma` `vlib__andb_split`
- `Lemma` `vlib__nandb_split`
- `Lemma` `vlib__orb_split`
- `Lemma` `vlib__norb_split`
- `Lemma` `vlib__eqb_split`
- `Lemma` `vlib__beq_rewrite`
- `Lemma` `vlib__leq_split`
- `Lemma` `vlib__ltn_split1`
- `Lemma` `vlib__ltn_split2`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Basic Boolean lemmas of the classic tactic library (based on Viktor Vafeiadis'
`Vbase.v`).

Representation notes:
* The source's tactics (`done`, `des`, `desf`, `clarify`, …), hint databases and
  the notation `eqxx := beq_refl` have no Lean counterpart; only the named lemmas
  are declarations.  The source re-exports the official v0.6 `util/tactics.v`,
  mirrored by the `export` of the accepted `Prosa.Util.Tactics` below.
* The source sets `Implicit Arguments`, so every argument determined by a later
  one is implicit (`About` prints `[T]`, `[b1 b2]`, …); they are Lean implicit
  binders.
* `x == y` is `decide (x = y)`; `is_true b` is `b = true`; `negb b` is `!b`; the
  Boolean chain `x1 <= x2 <= x3` is `(decide (x1 ≤ x2) && decide (x2 ≤ x3)) = true`
  and `x < y` is MathComp's `x.+1 <= y`, written `x < y`.
* `reflect P b` is the informative `BoolReflect P b` (as in the accepted v0.6
  files), defined below as a Lean helper.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: accepted.
