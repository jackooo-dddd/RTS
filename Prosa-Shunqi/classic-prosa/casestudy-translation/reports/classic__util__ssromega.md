# Report: `classic/util/ssromega.v` (rank 3)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/ssromega.v` |
| sha256 | `b7b0744ecd1211079afed5ade93c760dd15e3960dbc1fcf0518a753ff94872c1` |
| Lean module | `Prosa/Classic/Util/Ssromega.lean` (namespace `Prosa.Classic.Util.Ssromega`) |
| Tier / layer | S / 0 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (0 source → Lean, same names)


Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

`classic/util/ssromega.v` defines only the Ltac tactics `arith_hypo_ssrnat2coqnat`,
`arith_goal_ssrnat2coqnat` and `ssromega` (no named declaration; the module has no
constant in Rocq's `Print Module`).  Lean proofs use `omega` instead, so this module
is intentionally empty; it exists so that the classic utility aggregator
(`Prosa.Classic.Util.All`) mirrors the source's export list.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: accepted.
