# Report: `classic/util/counting.v` (rank 14)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/counting.v` |
| sha256 | `73dab4e21056ece3aaded263fa5997802a3ca019cdc9e554ff33b83adb6bef31` |
| Lean module | `Prosa/Classic/Util/Counting.lean` (namespace `Prosa.Classic.Util.Counting`) |
| Tier / layer | S / 3 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (5 source → Lean, same names)

- `Lemma` `count_or`
- `Lemma` `sub_in_count`
- `Lemma` `count_sub_uniqr`
- `Lemma` `count_pred_inj`
- `Lemma` `count_exists`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Additional lemmas about counting.

Representation notes: `count P l` is `List.countP P l`; `{subset l1 <= l2}` is
`∀ x, x ∈ l1 → x ∈ l2`; Boolean predicates in proposition position are
`P x = true`; `[exists x in 'I_n, P y x]` is `(List.finRange n).any (P y)` (as
in `ord_quantifier`), and `widen_ord (leqnSn n)` / `ord_max` are
`Fin.castSucc` / `Fin.last n`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
