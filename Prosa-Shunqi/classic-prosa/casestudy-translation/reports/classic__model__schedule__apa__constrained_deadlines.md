# Report: `classic/model/schedule/apa/constrained_deadlines.v` (rank 41)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/apa/constrained_deadlines.v` |
| sha256 | `1b05e97239bacbe3c37a657d84a4367d0e39b4e3c88c4e1fecb222354ba3b37f` |
| Lean module | `Prosa/Classic/Model/Schedule/Apa/ConstrainedDeadlines.lean` (namespace `Prosa.Classic.Model.Schedule.Apa.ConstrainedDeadlines`) |
| Tier / layer | S / 14 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (4 source → Lean, same names)

- `Lemma` `ConstrainedDeadlines.platform_at_most_one_pending_job_of_each_task`
- `Definition` `ConstrainedDeadlines.scheduled_task_with_higher_eq_priority`
- `Lemma` `ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_interfering_tasks`
- `Lemma` `ConstrainedDeadlines.platform_fp_no_multiple_jobs_of_tsk`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `pending_iff`.

## Representation notes

Absence of multiple pending jobs of the same task under constrained deadlines, in
APA schedules (Rocq module `ConstrainedDeadlines`, `classic/model/schedule/apa`).

Unlike its global counterpart, this source file has no counting lemmas: it only
proves the uniqueness lemmas.  The section-local `Let hp_task_in alpha'` is
unfolded to `higher_priority_task_in alpha higher_eq_priority tsk alpha'` (with the
section `tsk`).  Binder lists follow the Rocq contract: as in the global file,
`scheduled_task_with_higher_eq_priority` takes the section `tsk` and `t` followed by its
own parameter `tsk`, named `tsk'` here; unlike the global file, that parameter is used,
in `hp_task_in (alpha tsk') tsk_other` (checked with `Print` in the official build:
`hp_task_in (alpha tsk0) tsk_other`).

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
