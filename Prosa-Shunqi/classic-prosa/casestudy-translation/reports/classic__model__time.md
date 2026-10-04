# Report: `classic/model/time.v` (rank 1)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/time.v` |
| sha256 | `0510fd6b0a75ac638518f5952f4f9c011bd9c321f0d6b57324a3ebe4ccc9f216` |
| Lean module | `Prosa/Classic/Model/Time.lean` (namespace `Prosa.Classic.Model.Time`) |
| Tier / layer | S / 0 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (3 source → Lean, same names)

- `Definition` `Time.time`
- `Definition` `Time.duration`
- `Definition` `Time.instant`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Classic Prosa's discrete time.  The source wraps its definitions in
`Module Time`; the Rocq module path is mirrored by the Lean namespace
`Prosa.Classic.Model.Time.Time`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-01: accepted.
- 2026-10-02: accepted.
