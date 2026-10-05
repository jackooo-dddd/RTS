# `analysis/abstract/IBF/task.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `nonself` | Definition | `Prosa.Analysis.Abstract.IBF.Task.nonself` | `nonself_correspondence` | [view](3_printed_declarations/nonself.md) |
| `task_interference` | Definition | `Prosa.Analysis.Abstract.IBF.Task.task_interference` | `task_interference_correspondence` | [view](3_printed_declarations/task_interference.md) |
| `cumul_task_interference` | Definition | `Prosa.Analysis.Abstract.IBF.Task.cumul_task_interference` | `cumul_task_interference_correspondence` | [view](3_printed_declarations/cumul_task_interference.md) |
| `task_interference_is_bounded_by` | Definition | `Prosa.Analysis.Abstract.IBF.Task.task_interference_is_bounded_by` | `task_interference_is_bounded_by_correspondence` | [view](3_printed_declarations/task_interference_is_bounded_by.md) |
| `interference_and_workload_consistent_with_sequential_tasks` | Definition | `Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks` | `interference_and_workload_consistent_with_sequential_tasks_correspondence` | [view](3_printed_declarations/interference_and_workload_consistent_with_sequential_tasks.md) |
| `completed_before_beginning_of_busy_interval` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.completed_before_beginning_of_busy_interval` | `completed_before_beginning_of_busy_interval_correspondence` | [view](3_printed_declarations/completed_before_beginning_of_busy_interval.md) |
| `arrives_after_beginning_of_busy_interval` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.arrives_after_beginning_of_busy_interval` | `arrives_after_beginning_of_busy_interval_correspondence` | [view](3_printed_declarations/arrives_after_beginning_of_busy_interval.md) |
| `interference_plus_sched_le_serv_of_task_plus_task_interference_idle` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.interference_plus_sched_le_serv_of_task_plus_task_interference_idle` | `interference_plus_sched_le_serv_of_task_plus_task_interference_idle_correspondence` | [view](3_printed_declarations/interference_plus_sched_le_serv_of_task_plus_task_interference_idle.md) |
| `interference_plus_sched_le_serv_of_task_plus_task_interference_task` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.interference_plus_sched_le_serv_of_task_plus_task_interference_task` | `interference_plus_sched_le_serv_of_task_plus_task_interference_task_correspondence` | [view](3_printed_declarations/interference_plus_sched_le_serv_of_task_plus_task_interference_task.md) |
| `interference_plus_sched_le_serv_of_task_plus_task_interference_job` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.interference_plus_sched_le_serv_of_task_plus_task_interference_job` | `interference_plus_sched_le_serv_of_task_plus_task_interference_job_correspondence` | [view](3_printed_declarations/interference_plus_sched_le_serv_of_task_plus_task_interference_job.md) |
| `interference_and_service_eq_1` | Fact | `Prosa.Analysis.Abstract.IBF.Task.interference_and_service_eq_1` | `interference_and_service_eq_1_correspondence` | [view](3_printed_declarations/interference_and_service_eq_1.md) |
| `interference_plus_sched_le_serv_of_task_plus_task_interference_j` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.interference_plus_sched_le_serv_of_task_plus_task_interference_j` | `interference_plus_sched_le_serv_of_task_plus_task_interference_j_correspondence` | [view](3_printed_declarations/interference_plus_sched_le_serv_of_task_plus_task_interference_j.md) |
| `interference_plus_sched_le_serv_of_task_plus_task_interference` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.interference_plus_sched_le_serv_of_task_plus_task_interference` | `interference_plus_sched_le_serv_of_task_plus_task_interference_correspondence` | [view](3_printed_declarations/interference_plus_sched_le_serv_of_task_plus_task_interference.md) |
| `cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference` | `cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference_correspondence` | [view](3_printed_declarations/cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference.md) |
| `serv_of_task_le_workload_of_task_plus` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.serv_of_task_le_workload_of_task_plus` | `serv_of_task_le_workload_of_task_plus_correspondence` | [view](3_printed_declarations/serv_of_task_le_workload_of_task_plus.md) |
| `cumulative_job_interference_le_task_interference_bound` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.cumulative_job_interference_le_task_interference_bound` | `cumulative_job_interference_le_task_interference_bound_correspondence` | [view](3_printed_declarations/cumulative_job_interference_le_task_interference_bound.md) |
| `cumulative_job_interference_bound` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.cumulative_job_interference_bound` | `cumulative_job_interference_bound_correspondence` | [view](3_printed_declarations/cumulative_job_interference_bound.md) |
| `task_IBF_implies_job_IBF` | Lemma | `Prosa.Analysis.Abstract.IBF.Task.task_IBF_implies_job_IBF` | `task_IBF_implies_job_IBF_correspondence` | [view](3_printed_declarations/task_IBF_implies_job_IBF.md) |

## Certificates

| Module | Role |
|---|---|
| [`IbfTaskCorrespondence`](4_correspondence/IbfTaskCorrespondence.v) | The common inequality of the case lemmas. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
