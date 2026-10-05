# `implementation/refinements/task.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `Task` | Definition | `Prosa.Implementation.Refinements.Task.Task` | `Task_source_total, Task_target_total` | [view](3_printed_declarations/Task.md) |
| `Job` | Definition | `Prosa.Implementation.Refinements.Task.Job` | `Job_source_total, Job_target_total` | [view](3_printed_declarations/Job.md) |
| `task_T` | Structure | `Prosa.Implementation.Refinements.Task.task_T` | `task_T_source_total, task_T_target_total` | [view](3_printed_declarations/task_T.md) |
| `task_eqdef_T` | Definition | `Prosa.Implementation.Refinements.Task.task_eqdef_T` | `task_eqdef_T_correspondence` | [view](3_printed_declarations/task_eqdef_T.md) |
| `inter_arrival_to_extrapolated_arrival_curve_T` | Definition | `Prosa.Implementation.Refinements.Task.inter_arrival_to_extrapolated_arrival_curve_T` | `inter_arrival_to_extrapolated_arrival_curve_T_correspondence` | [view](3_printed_declarations/inter_arrival_to_extrapolated_arrival_curve_T.md) |
| `get_extrapolated_arrival_curve_T` | Definition | `Prosa.Implementation.Refinements.Task.get_extrapolated_arrival_curve_T` | `get_extrapolated_arrival_curve_T_correspondence` | [view](3_printed_declarations/get_extrapolated_arrival_curve_T.md) |
| `ConcreteMaxArrivals_T` | Definition | `Prosa.Implementation.Refinements.Task.ConcreteMaxArrivals_T` | `ConcreteMaxArrivals_T_correspondence` | [view](3_printed_declarations/ConcreteMaxArrivals_T.md) |
| `task_rbf_T` | Definition | `Prosa.Implementation.Refinements.Task.task_rbf_T` | `task_rbf_T_correspondence` | [view](3_printed_declarations/task_rbf_T.md) |
| `valid_arrivals_T` | Definition | `Prosa.Implementation.Refinements.Task.valid_arrivals_T` | `valid_arrivals_T_correspondence` | [view](3_printed_declarations/valid_arrivals_T.md) |
| `get_horizon_of_task_T` | Definition | `Prosa.Implementation.Refinements.Task.get_horizon_of_task_T` | `get_horizon_of_task_T_correspondence` | [view](3_printed_declarations/get_horizon_of_task_T.md) |
| `get_time_steps_of_task_T` | Definition | `Prosa.Implementation.Refinements.Task.get_time_steps_of_task_T` | `get_time_steps_of_task_T_correspondence` | [view](3_printed_declarations/get_time_steps_of_task_T.md) |
| `time_steps_with_offset_T` | Definition | `Prosa.Implementation.Refinements.Task.time_steps_with_offset_T` | `time_steps_with_offset_T_correspondence` | [view](3_printed_declarations/time_steps_with_offset_T.md) |
| `repeat_steps_with_offset_T` | Definition | `Prosa.Implementation.Refinements.Task.repeat_steps_with_offset_T` | `repeat_steps_with_offset_T_correspondence` | [view](3_printed_declarations/repeat_steps_with_offset_T.md) |
| `taskT_to_task` | Definition | `Prosa.Implementation.Refinements.Task.taskT_to_task` | `taskT_to_task_correspondence` | [view](3_printed_declarations/taskT_to_task.md) |
| `Rtask` | Definition | `Prosa.Implementation.Refinements.Task.Rtask` | `Rtask_correspondence` | [view](3_printed_declarations/Rtask.md) |
| `task_to_taskT` | Definition | `Prosa.Implementation.Refinements.Task.task_to_taskT` | `task_to_taskT_correspondence` | [view](3_printed_declarations/task_to_taskT.md) |
| `refine_task` | Instance | `Prosa.Implementation.Refinements.Task.refine_task` | `refine_task_correspondence` | [view](3_printed_declarations/refine_task.md) |
| `refine_task_id` | Instance | `Prosa.Implementation.Refinements.Task.refine_task_id` | `refine_task_id_correspondence` | [view](3_printed_declarations/refine_task_id.md) |
| `refine_task_cost` | Instance | `Prosa.Implementation.Refinements.Task.refine_task_cost` | `refine_task_cost_correspondence` | [view](3_printed_declarations/refine_task_cost.md) |
| `refine_task_arrival` | Instance | `Prosa.Implementation.Refinements.Task.refine_task_arrival` | `refine_task_arrival_correspondence` | [view](3_printed_declarations/refine_task_arrival.md) |
| `refine_task_deadline` | Instance | `Prosa.Implementation.Refinements.Task.refine_task_deadline` | `refine_task_deadline_correspondence` | [view](3_printed_declarations/refine_task_deadline.md) |
| `refine_task_priority` | Instance | `Prosa.Implementation.Refinements.Task.refine_task_priority` | `refine_task_priority_correspondence` | [view](3_printed_declarations/refine_task_priority.md) |
| `refine_Periodic` | Instance | `Prosa.Implementation.Refinements.Task.refine_Periodic` | `refine_Periodic_correspondence` | [view](3_printed_declarations/refine_Periodic.md) |
| `refine_Sporadic` | Instance | `Prosa.Implementation.Refinements.Task.refine_Sporadic` | `refine_Sporadic_correspondence` | [view](3_printed_declarations/refine_Sporadic.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtBase`](4_correspondence/RtBase.v) | Correspondences for `implementation/refinements/refinements.v`. |
| [`RtArrivalBound`](4_correspondence/RtArrivalBound.v) | Correspondences for `implementation/refinements/arrival_bound.v`. |
| [`RefTaskCorrespondence`](4_correspondence/RefTaskCorrespondence.v) | Correspondences for `implementation/refinements/task.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | — |
| Imported Lean axioms | — |
| Definitional UIP | `HEq`, `eq` |
| Rocq primitives | — |
