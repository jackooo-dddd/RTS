# `implementation/definitions/task.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `concrete_task` | Structure | `Prosa.Implementation.Definitions.Task.concrete_task` | `concrete_task_source_total, concrete_task_target_total` | [view](3_printed_declarations/concrete_task.md) |
| `task_eqdef` | Definition | `Prosa.Implementation.Definitions.Task.task_eqdef` | `task_eqdef_correspondence` | [view](3_printed_declarations/task_eqdef.md) |
| `eqn_task` | Lemma | `Prosa.Implementation.Definitions.Task.eqn_task` | `eqn_task_correspondence` | [view](3_printed_declarations/eqn_task.md) |
| `concrete_job` | Record | `Prosa.Implementation.Definitions.Task.concrete_job` | `concrete_job_source_total, concrete_job_target_total` | [view](3_printed_declarations/concrete_job.md) |
| `get_arrival_curve_prefix` | Definition | `Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix` | `get_arrival_curve_prefix_correspondence` | [view](3_printed_declarations/get_arrival_curve_prefix.md) |
| `concrete_max_arrivals` | Definition | `Prosa.Implementation.Definitions.Task.concrete_max_arrivals` | `concrete_max_arrivals_correspondence` | [view](3_printed_declarations/concrete_max_arrivals.md) |
| `job_eqdef` | Definition | `Prosa.Implementation.Definitions.Task.job_eqdef` | `job_eqdef_correspondence` | [view](3_printed_declarations/job_eqdef.md) |
| `eqn_job` | Lemma | `Prosa.Implementation.Definitions.Task.eqn_job` | `eqn_job_correspondence` | [view](3_printed_declarations/eqn_job.md) |
| `TaskCost` | Instance | `Prosa.Implementation.Definitions.Task.TaskCost` | `TaskCost_correspondence` | [view](3_printed_declarations/TaskCost.md) |
| `TaskPriority` | Instance | `Prosa.Implementation.Definitions.Task.TaskPriority` | `TaskPriority_correspondence` | [view](3_printed_declarations/TaskPriority.md) |
| `TaskDeadline` | Instance | `Prosa.Implementation.Definitions.Task.TaskDeadline` | `TaskDeadline_correspondence` | [view](3_printed_declarations/TaskDeadline.md) |
| `ConcreteMaxArrivals` | Instance | `Prosa.Implementation.Definitions.Task.ConcreteMaxArrivals` | `ConcreteMaxArrivals_correspondence` | [view](3_printed_declarations/ConcreteMaxArrivals.md) |
| `JobTask` | Instance | `Prosa.Implementation.Definitions.Task.JobTask` | `JobTask_correspondence` | [view](3_printed_declarations/JobTask.md) |
| `JobArrival` | Instance | `Prosa.Implementation.Definitions.Task.JobArrival` | `JobArrival_correspondence` | [view](3_printed_declarations/JobArrival.md) |
| `JobCost` | Instance | `Prosa.Implementation.Definitions.Task.JobCost` | `JobCost_correspondence` | [view](3_printed_declarations/JobCost.md) |

## Certificates

| Module | Role |
|---|---|
| [`EacFullCorrespondence`](4_correspondence/EacFullCorrespondence.v) | An operation-level representation relation for the actual imported Lean product/list constructors. |
| [`AbCorrespondence`](4_correspondence/AbCorrespondence.v) | The prefix type is the extrapolated-curve prefix of this same export, so the accepted adapter between the two separate earlier exports is replaced by the EAC prefix maps and roundtrips. |
| [`ImplTaskCorrespondence`](4_correspondence/ImplTaskCorrespondence.v) | Correspondences for `implementation/definitions/task.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
