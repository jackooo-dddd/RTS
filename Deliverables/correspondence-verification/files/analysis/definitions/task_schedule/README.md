# `analysis/definitions/task_schedule.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `scheduled_jobs_of_task_at` | Definition | `Prosa.Analysis.Definitions.TaskSchedule.scheduled_jobs_of_task_at` | `scheduled_jobs_of_task_at_correspondence` | [view](3_printed_declarations/scheduled_jobs_of_task_at.md) |
| `task_scheduled_at` | Definition | `Prosa.Analysis.Definitions.TaskSchedule.task_scheduled_at` | `task_scheduled_at_correspondence` | [view](3_printed_declarations/task_scheduled_at.md) |
| `task_service_at` | Definition | `Prosa.Analysis.Definitions.TaskSchedule.task_service_at` | `task_service_at_correspondence` | [view](3_printed_declarations/task_service_at.md) |
| `task_service_during` | Definition | `Prosa.Analysis.Definitions.TaskSchedule.task_service_during` | `task_service_during_correspondence` | [view](3_printed_declarations/task_service_during.md) |
| `task_service` | Definition | `Prosa.Analysis.Definitions.TaskSchedule.task_service` | `task_service_correspondence` | [view](3_printed_declarations/task_service.md) |
| `served_jobs_of_task_at` | Definition | `Prosa.Analysis.Definitions.TaskSchedule.served_jobs_of_task_at` | `served_jobs_of_task_at_correspondence` | [view](3_printed_declarations/served_jobs_of_task_at.md) |
| `task_served_at` | Definition | `Prosa.Analysis.Definitions.TaskSchedule.task_served_at` | `task_served_at_correspondence` | [view](3_printed_declarations/task_served_at.md) |

## Certificates

| Module | Role |
|---|---|
| [`TaskScheduleExactTypeGuards`](4_correspondence/TaskScheduleExactTypeGuards.v) | Both signatures are elaborated afresh from the pinned source and the actual imported Lean artifact; no postulated type equality is used. |
| [`ArrivalSequenceOperations`](4_correspondence/ArrivalSequenceOperations.v) | Minimal operation-level correspondence layer for the actual compiled Arrival Sequence artifact. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
