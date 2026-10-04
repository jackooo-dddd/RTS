# Report: `classic/util/div_mod.v` (rank 15)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/div_mod.v` |
| sha256 | `8c8069433f2727dd357712b3a7963174d0a331058786d885147bc5c3a2ad5a29` |
| Lean module | `Prosa/Classic/Util/DivMod.lean` (namespace `Prosa.Classic.Util.DivMod`) |
| Tier / layer | S / 3 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (17 source → Lean, same names)

- `Definition` `div_floor`
- `Definition` `div_ceil`
- `Lemma` `ltn_div_trunc`
- `Lemma` `subndiv_eq_mod`
- `Lemma` `divSn_cases`
- `Lemma` `ceil_neq0`
- `Lemma` `leq_divceil2r`
- `Lemma` `eq_modDl`
- `Lemma` `eq_modDr`
- `Lemma` `modulo_exists`
- `Lemma` `modnS_eq`
- `Lemma` `modnSor'`
- `Lemma` `modnSor`
- `Lemma` `modulo_cases`
- `Lemma` `ceil_eq1`
- `Lemma` `ceil_suba`
- `Lemma` `mod_eq`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `mod_add_div'`, `succ_mod_cases`.

## Representation notes

Division and modulo.  The source re-exports `prosa.util.div_mod` (imported above)
and declares its own `div_floor`/`div_ceil` in the classic namespace; they are
kept here with exactly the form of the accepted v0.6 definitions.

Representation notes: `m %/ d` and `m %% d` are Lean's `/` and `%` on `Nat`
(both give the same value as MathComp for `d = 0`); `y %| x` is `y ∣ x`;
`a = b %[mod d]` is `a % d = b % d`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
