# Report: `classic/util/all.v` (rank 21)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/all.v` |
| sha256 | `3fe26417c92d71b8e076bff6a91fe262f8aa997091cee03aa7d01029fd8fcff1` |
| Lean module | `Prosa/Classic/Util/All.lean` (namespace `Prosa.Classic.Util.All`) |
| Tier / layer | S / 5 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (0 source → Lean, same names)


Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

`classic/util/all.v` is the classic utility aggregator: only `Require Export`
commands (no declaration).  The Lean module imports exactly the corresponding
translated modules, in the source order (the v0.6 `util/epsilon.v` maps to the
accepted `Prosa.Util.Epsilon`).

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
