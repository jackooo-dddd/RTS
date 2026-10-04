# Report: `classic/util/ord_quantifier.v` (rank 11)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/ord_quantifier.v` |
| sha256 | `4cb2c3a2f476d36f2283a97777addc4ec00784bbaf2feea802d196590a7257bf` |
| Lean module | `Prosa/Classic/Util/OrdQuantifier.lean` (namespace `Prosa.Classic.Util.OrdQuantifier`) |
| Tier / layer | S / 2 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (4 source → Lean, same names)

- `Lemma` `exists_ord0`
- `Lemma` `exists_recr`
- `Lemma` `forall_ord0`
- `Lemma` `forall_recr`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Lemmas about Boolean quantifiers over ordinals.

Representation notes: `'I_n` is `Fin n`; `ord_max : 'I_n.+1` is `Fin.last n`;
`widen_ord (leqnSn n)` is `Fin.castSucc`.  The finite Boolean quantifiers
`[exists x in 'I_n, P x]` / `[forall x in 'I_n, P x]` are the direct Boolean
enumerations `(List.finRange n).any P` / `(List.finRange n).all P`.  The source's
Ltac helpers `simpl_exists_ord` / `simpl_forall_ord` have no Lean counterpart.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
