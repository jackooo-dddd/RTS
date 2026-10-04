# Report: `classic/model/schedule/global/schedulability.v` (rank 31)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/global/schedulability.v` |
| sha256 | `db20b1145497d5a5bd4482ae0b27648b8296add9fdeec8e6f36c5b71f36e24a0` |
| Lean module | `Prosa/Classic/Model/Schedule/Global/Schedulability.lean` (namespace `Prosa.Classic.Model.Schedule.Global.Schedulability`) |
| Tier / layer | S / 10 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (7 source → Lean, same names)

- `Definition` `Schedulability.job_misses_no_deadline`
- `Definition` `Schedulability.task_misses_no_deadline`
- `Definition` `Schedulability.task_misses_no_deadline_before`
- `Lemma` `Schedulability.service_after_job_deadline_zero`
- `Lemma` `Schedulability.cumulative_service_after_job_deadline_zero`
- `Lemma` `Schedulability.service_after_task_deadline_zero`
- `Lemma` `Schedulability.cumulative_service_after_task_deadline_zero`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Schedulability (Rocq module `Schedulability`).  Binder lists follow the Rocq
contract.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
