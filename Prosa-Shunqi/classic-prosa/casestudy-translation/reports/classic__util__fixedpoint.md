# Report: `classic/util/fixedpoint.v` (rank 16)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/fixedpoint.v` |
| sha256 | `b5de1428301cecb92da563150c6099495fb989685b20420eab80a4691eb36cfd` |
| Lean module | `Prosa/Classic/Util/Fixedpoint.lean` (namespace `Prosa.Classic.Util.Fixedpoint`) |
| Tier / layer | S / 3 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (10 source → Lean, same names)

- `Lemma` `iter_fix`
- `Lemma` `fun_mon_iter_mon`
- `Lemma` `fun_mon_iter_mon_helper`
- `Lemma` `fun_mon_iter_mon_generic`
- `Definition` `monotone`
- `Fixpoint` `iter_fixpoint`
- `Lemma` `iter_fixpoint_cases`
- `Lemma` `iter_fixpoint_ind`
- `Lemma` `iter_fixpoint_ge_min`
- `Lemma` `iter_fixpoint_ge_bottom`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `iter_fixpoint_succ_fix`, `iter_fixpoint_succ_step`.

## Representation notes

Fixed-point iterations.

Representation notes:
* MathComp's `iter n f x` (`iter (S n) f x = f (iter n f x)`) is the Lean helper
  `iter` below, with the same recursion and argument order (Lean's `Nat.iterate`
  unfolds on the inside instead).
* A relation `rel T` is `T → T → Bool`; MathComp's `reflexive R` and `transitive R`
  are unfolded: `∀ x, R x x = true` and `∀ y x z, R x y = true → R y z = true → R x z
  = true` (MathComp's binder order).
* `iter_fixpoint_ind` has a `Type`-valued motive (`P : T -> Type`), so it is a Lean
  definition over `P : T → Sort w`.
* `x == y` is `decide (x = y)`; Boolean statements in proposition position are `… = true`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
