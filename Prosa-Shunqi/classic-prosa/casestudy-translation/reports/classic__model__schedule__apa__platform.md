# Report: `classic/model/schedule/apa/platform.v` (rank 37)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/apa/platform.v` |
| sha256 | `ec1e254566a597b0f94dbe1ac563ecaa30198a0d29c17cf6878ac52bf399f7a9` |
| Lean module | `Prosa/Classic/Model/Schedule/Apa/Platform.lean` (namespace `Prosa.Classic.Model.Schedule.Apa.Platform`) |
| Tier / layer | S / 13 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (5 source → Lean, same names)

- `Definition` `Platform.apa_work_conserving`
- `Definition` `Platform.respects_affinity`
- `Definition` `Platform.respects_FP_policy_under_weak_APA`
- `Definition` `Platform.respects_JLFP_policy_under_weak_APA`
- `Definition` `Platform.respects_JLDP_policy_under_weak_APA`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Platform properties under processor affinities (Rocq module `Platform` of
`classic/model/schedule/apa`).  Binder lists follow the Rocq contract.
Boolean predicates in proposition position are `… = true`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
