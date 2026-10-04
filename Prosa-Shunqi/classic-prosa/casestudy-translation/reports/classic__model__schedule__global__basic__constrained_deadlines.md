# Report: `classic/model/schedule/global/basic/constrained_deadlines.v` (rank 42)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/global/basic/constrained_deadlines.v` |
| sha256 | `39e1e4ecba165e08307a7a62ef765812d15e6a7a7881e6051022d9ba16576f3f` |
| Lean module | `Prosa/Classic/Model/Schedule/Global/Basic/ConstrainedDeadlines.lean` (namespace `Prosa.Classic.Model.Schedule.Global.Basic.ConstrainedDeadlines`) |
| Tier / layer | S / 14 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (6 source → Lean, same names)

- `Lemma` `ConstrainedDeadlines.platform_at_most_one_pending_job_of_each_task`
- `Lemma` `ConstrainedDeadlines.platform_cpus_busy_with_interfering_tasks`
- `Definition` `ConstrainedDeadlines.scheduled_task_with_higher_eq_priority`
- `Lemma` `ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_interfering_tasks`
- `Lemma` `ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_tsk`
- `Lemma` `ConstrainedDeadlines.platform_fp_cpus_busy_with_interfering_tasks`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `mem_jobs_scheduled_iff`, `scheduled_iff_exists`, `pending_iff`, `task_is_scheduled_of_scheduled`, `count_task_is_scheduled_le`.

## Representation notes

Absence of multiple pending jobs of the same task under constrained deadlines, in
global schedules (Rocq module `ConstrainedDeadlines`).

Representation notes: `count P ts` over a task set is `ts.val.countP P`; the
section-local `Let scheduled_task_other_than tsk tsk_other` is unfolded to
`task_is_scheduled job_task sched tsk_other t && !decide (tsk_other = tsk)` and
`Let is_hp_task` to `higher_priority_task higher_eq_priority tsk`.  Binder lists
follow the Rocq contract, which records exactly the section variables each
declaration abstracts (e.g. `platform_at_most_one_pending_job_of_each_task` takes
`H_valid_task` and `H_job_of_tsk`, and `scheduled_task_with_higher_eq_priority`
takes the section `tsk` and `t` followed by its own, unused, parameter `tsk`,
named `_tsk` here).

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
