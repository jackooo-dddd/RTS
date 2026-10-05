# `model/task/arrival/task_max_inter_arrival.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `TaskMaxInterArrival` | Class | `Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival` | `TaskMaxInterArrival_source_total, TaskMaxInterArrival_target_total` | [view](3_printed_declarations/TaskMaxInterArrival.md) |
| `positive_task_max_inter_arrival_time` | Definition | `Prosa.Model.Task.Arrival.Task_max_inter_arrival.positive_task_max_inter_arrival_time` | `positive_task_max_inter_arrival_time_correspondence` | [view](3_printed_declarations/positive_task_max_inter_arrival_time.md) |
| `arr_sep_task_max_inter_arrival` | Definition | `Prosa.Model.Task.Arrival.Task_max_inter_arrival.arr_sep_task_max_inter_arrival` | `arr_sep_task_max_inter_arrival_correspondence` | [view](3_printed_declarations/arr_sep_task_max_inter_arrival.md) |
| `valid_task_max_inter_arrival_time` | Definition | `Prosa.Model.Task.Arrival.Task_max_inter_arrival.valid_task_max_inter_arrival_time` | `valid_task_max_inter_arrival_time_correspondence` | [view](3_printed_declarations/valid_task_max_inter_arrival_time.md) |
| `taskset_respects_task_max_inter_arrival_model` | Definition | `Prosa.Model.Task.Arrival.Task_max_inter_arrival.taskset_respects_task_max_inter_arrival_model` | `taskset_respects_task_max_inter_arrival_model_correspondence` | [view](3_printed_declarations/taskset_respects_task_max_inter_arrival_model.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
