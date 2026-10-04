# Report: `classic/util/pick.v` (rank 2)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/pick.v` |
| sha256 | `004cfa0079ec10554593e28a2241dde86e8fdca6911fdd3d911afd091d0162cd` |
| Lean module | `Prosa/Classic/Util/Pick.lean` (namespace `Prosa.Classic.Util.Pick`) |
| Tier / layer | S / 0 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (17 source → Lean, same names)

- `Definition` `default0`
- `Definition` `arg_pred_nat`
- `Definition` `pred_min_nat`
- `Definition` `pred_max_nat`
- `Definition` `to_pred_ord`
- `Definition` `pick_any`
- `Definition` `pick_min`
- `Definition` `pick_max`
- `Lemma` `pick_any_holds`
- `Lemma` `pick_min_ltn`
- `Lemma` `pick_min_holds`
- `Lemma` `pick_max_ltn`
- `Lemma` `pick_max_holds`
- `Lemma` `pick_any_pred`
- `Lemma` `pick_min_pred`
- `Lemma` `pick_max_pred`
- `Lemma` `pick_min_compare`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `find?_finRange_some`, `arg_pred_nat_iff`, `pick_min_spec`, `pick_max_spec`.

## Representation notes

Picking numbers in an interval `[0, n)`.

Representation notes:
* `'I_n` is `Fin n`; a predicate `pred T` (and MathComp's `simpl_pred T`) is a
  Boolean function `T → Bool`.
* MathComp's `pick P` on `'I_n` is the first ordinal of `enum 'I_n` (increasing
  order) that satisfies `P`, i.e. `(List.finRange n).find? P`.
* `[pred i | P i & [forall j : 'I_n, P j ==> ord i j]]` is
  `fun i => P i && (List.finRange n).all (fun j => !P j || ord i j)`; the
  relation of `arg_pred_nat` is on ordinals, and `leq`/`geq` used there compare
  the ordinals through `nat_of_ord` (`i.val`).
* The `[pick-… x … N | P]` notations are parsing-only and have no Lean counterpart.
* Boolean predicates in proposition position are `p x = true`; `x < n` is the Nat order.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-01: accepted.
- 2026-10-02: accepted.
