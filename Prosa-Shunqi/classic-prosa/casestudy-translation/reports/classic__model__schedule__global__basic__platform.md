# Report: `classic/model/schedule/global/basic/platform.v` (rank 38)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/global/basic/platform.v` |
| sha256 | `0c99a19bbf63ef799c6540c7f6cff897637404243fefbf24620f91ac7d9745d9` |
| Lean module | `Prosa/Classic/Model/Schedule/Global/Basic/Platform.lean` (namespace `Prosa.Classic.Model.Schedule.Global.Basic.Platform`) |
| Tier / layer | S / 13 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (6 source → Lean, same names)

- `Definition` `Platform.work_conserving`
- `Definition` `Platform.work_conserving_count`
- `Definition` `Platform.respects_FP_policy`
- `Definition` `Platform.respects_JLFP_policy`
- `Definition` `Platform.respects_JLDP_policy`
- `Lemma` `Platform.work_conserving_eq_work_conserving_count`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `size_scheduled_eq_iff`.

## Representation notes

Platform properties of global schedules (Rocq module `Platform`): work
conservation and compliance with FP/JLFP/JLDP policies.  Binder lists follow the
Rocq contract (`work_conserving_eq_work_conserving_count` does not take the
section hypothesis `H_valid_job_parameters`, which its proof does not use).
Boolean predicates in proposition position are `… = true`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
