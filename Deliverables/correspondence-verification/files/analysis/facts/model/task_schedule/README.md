# `analysis/facts/model/task_schedule.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_served_task_scheduled` | Lemma | `Prosa.Analysis.Facts.Model.TaskSchedule.task_served_task_scheduled` | `task_served_task_scheduled_correspondence` | [view](3_printed_declarations/task_served_task_scheduled.md) |
| `task_served_eq_task_scheduled` | Lemma | `Prosa.Analysis.Facts.Model.TaskSchedule.task_served_eq_task_scheduled` | `task_served_eq_task_scheduled_correspondence` | [view](3_printed_declarations/task_served_eq_task_scheduled.md) |
| `no_task_scheduled_when_idle` | Lemma | `Prosa.Analysis.Facts.Model.TaskSchedule.no_task_scheduled_when_idle` | `no_task_scheduled_when_idle_correspondence` | [view](3_printed_declarations/no_task_scheduled_when_idle.md) |
| `no_task_served_when_idle` | Lemma | `Prosa.Analysis.Facts.Model.TaskSchedule.no_task_served_when_idle` | `no_task_served_when_idle_correspondence` | [view](3_printed_declarations/no_task_served_when_idle.md) |
| `job_of_scheduled_task` | Lemma | `Prosa.Analysis.Facts.Model.TaskSchedule.job_of_scheduled_task` | `job_of_scheduled_task_correspondence` | [view](3_printed_declarations/job_of_scheduled_task.md) |
| `job_of_task_scheduled` | Corollary | `Prosa.Analysis.Facts.Model.TaskSchedule.job_of_task_scheduled` | `job_of_task_scheduled_correspondence` | [view](3_printed_declarations/job_of_task_scheduled.md) |
| `job_of_other_task_scheduled` | Corollary | `Prosa.Analysis.Facts.Model.TaskSchedule.job_of_other_task_scheduled` | `job_of_other_task_scheduled_correspondence` | [view](3_printed_declarations/job_of_other_task_scheduled.md) |
| `job_of_other_task_scheduled'` | Corollary | `Prosa.Analysis.Facts.Model.TaskSchedule.job_of_other_task_scheduled'` | `job_of_other_task_scheduled'_correspondence` | [view](3_printed_declarations/job_of_other_task_scheduled'.md) |
| `job_of_task_not_served` | Corollary | `Prosa.Analysis.Facts.Model.TaskSchedule.job_of_task_not_served` | `job_of_task_not_served_correspondence` | [view](3_printed_declarations/job_of_task_not_served.md) |
| `task_served_at_eq_job_of_task` | Lemma | `Prosa.Analysis.Facts.Model.TaskSchedule.task_served_at_eq_job_of_task` | `task_served_at_eq_job_of_task_correspondence` | [view](3_printed_declarations/task_served_at_eq_job_of_task.md) |

## Certificates

| Module | Role |
|---|---|
| [`PStateCover`](4_correspondence/PStateCover.v) | Reusable processor-model infrastructure, extracted without change of proofs from the accepted certificate of `analysis/facts/model/ideal/service_of_jobs.v` (re-bound to this artifact's import): … |
| [`FactsTaskScheduleCorrespondence`](4_correspondence/FactsTaskScheduleCorrespondence.v) | Statement correspondences for `analysis/facts/model/task_schedule.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
