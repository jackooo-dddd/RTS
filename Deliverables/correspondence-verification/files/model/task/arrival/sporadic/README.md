# `model/task/arrival/sporadic.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `SporadicModel` | Class | `Prosa.Model.Task.Arrival.Sporadic.SporadicModel` | `sp_sporadic_model_import_certificate` | [view](3_printed_declarations/SporadicModel.md) |
| `valid_task_min_inter_arrival_time` | Definition | `Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time` | `sp_valid_task_min_inter_arrival_time_canonical` | [view](3_printed_declarations/valid_task_min_inter_arrival_time.md) |
| `valid_taskset_inter_arrival_times` | Definition | `Prosa.Model.Task.Arrival.Sporadic.valid_taskset_inter_arrival_times` | `sp_valid_taskset_inter_arrival_times_canonical` | [view](3_printed_declarations/valid_taskset_inter_arrival_times.md) |
| `respects_sporadic_task_model` | Definition | `Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model` | `sp_respects_sporadic_task_model_canonical` | [view](3_printed_declarations/respects_sporadic_task_model.md) |
| `taskset_respects_sporadic_task_model` | Definition | `Prosa.Model.Task.Arrival.Sporadic.taskset_respects_sporadic_task_model` | `sp_taskset_respects_sporadic_task_model_canonical` | [view](3_printed_declarations/taskset_respects_sporadic_task_model.md) |

## Certificates

| Module | Role |
|---|---|
| [`SporadicOperations`](4_correspondence/SporadicOperations.v) | Sporadic target-local operation slice adapted from accepted ConceptOperations. |
| [`SporadicClasses`](4_correspondence/SporadicClasses.v) | Observable source/target interfaces for this exact imported artifact. |
| [`SporadicCorrespondence`](4_correspondence/SporadicCorrespondence.v) | All displayed target constants are from the actual compiled Sporadic.olean import. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
