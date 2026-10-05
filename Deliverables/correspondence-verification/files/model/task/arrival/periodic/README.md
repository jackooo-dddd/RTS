# `model/task/arrival/periodic.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `PeriodicModel` | Class | `Prosa.Model.Task.Arrival.Periodic.PeriodicModel` | `PeriodicModel_source_total, PeriodicModel_target_total` | [view](3_printed_declarations/PeriodicModel.md) |
| `valid_period` | Definition | `Prosa.Model.Task.Arrival.Periodic.valid_period` | `valid_period_correspondence` | [view](3_printed_declarations/valid_period.md) |
| `respects_periodic_task_model` | Definition | `Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model` | `respects_periodic_task_model_correspondence` | [view](3_printed_declarations/respects_periodic_task_model.md) |
| `valid_periods` | Definition | `Prosa.Model.Task.Arrival.Periodic.valid_periods` | `valid_periods_correspondence` | [view](3_printed_declarations/valid_periods.md) |
| `taskset_respects_periodic_task_model` | Definition | `Prosa.Model.Task.Arrival.Periodic.taskset_respects_periodic_task_model` | `taskset_respects_periodic_task_model_correspondence` | [view](3_printed_declarations/taskset_respects_periodic_task_model.md) |

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
