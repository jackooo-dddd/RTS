# Report: `classic/model/schedule/global/response_time.v` (rank 30)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/global/response_time.v` |
| sha256 | `4097d7cc34e5b4fbf35ef48457c1f3f79669d1e0bd7b947b57070f13e6a54952` |
| Lean module | `Prosa/Classic/Model/Schedule/Global/ResponseTime.lean` (namespace `Prosa.Classic.Model.Schedule.Global.ResponseTime`) |
| Tier / layer | S / 10 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (5 source → Lean, same names)

- `Definition` `ResponseTime.is_response_time_bound_of_task`
- `Lemma` `ResponseTime.service_after_job_rt_zero`
- `Lemma` `ResponseTime.cumulative_service_after_job_rt_zero`
- `Lemma` `ResponseTime.service_after_task_rt_zero`
- `Lemma` `ResponseTime.cumulative_service_after_task_rt_zero`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Response-time bounds (Rocq module `ResponseTime`).  The section-local
`job_has_completed_by := completed job_cost sched` is unfolded.  Binder lists
follow the Rocq contract (e.g. `service_after_job_rt_zero` does not take
`H_j_arrives`; the task-level lemmas do).

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
