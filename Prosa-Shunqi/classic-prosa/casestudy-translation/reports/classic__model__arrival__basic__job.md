# Report: `classic/model/arrival/basic/job.v` (rank 24)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/arrival/basic/job.v` |
| sha256 | `7089419d2609f1fe18d75417e0c73623b3138921ca83e4a7398475bdc5966fa5` |
| Lean module | `Prosa/Classic/Model/Arrival/Basic/Job.lean` (namespace `Prosa.Classic.Model.Arrival.Basic.Job`) |
| Tier / layer | S / 8 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (8 source → Lean, same names)

- `Definition` `Job.job_cost_positive`
- `Definition` `Job.job_deadline_positive`
- `Definition` `Job.job_cost_le_deadline`
- `Definition` `Job.valid_realtime_job`
- `Definition` `Job.job_cost_le_task_cost`
- `Definition` `Job.job_deadline_eq_task_deadline`
- `Definition` `Job.valid_sporadic_job`
- `Definition` `Job.cost_of_jobs_from_arrival_sequence_le_task_cost`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Properties of jobs (Rocq module `Job`).  Binder lists follow the Rocq contract,
including interleaved implicit carriers, e.g.
`valid_sporadic_job {sporadic_task} task_cost task_deadline {Job} job_cost job_deadline job_task j`.
Boolean comparisons are `Bool`; equalities and conjunctions are `Prop`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
