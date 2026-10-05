# `model/task/arrival/periodic_as_sporadic.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `periodic_as_sporadic` | Instance | `Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_as_sporadic` | `periodic_as_sporadic_correspondence` | [view](3_printed_declarations/periodic_as_sporadic.md) |
| `valid_period_is_valid_inter_arrival_time` | Remark | `Prosa.Model.Task.Arrival.PeriodicAsSporadic.valid_period_is_valid_inter_arrival_time` | `valid_period_is_valid_inter_arrival_time_correspondence` | [view](3_printed_declarations/valid_period_is_valid_inter_arrival_time.md) |
| `periodic_task_respects_sporadic_task_model` | Remark | `Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_task_respects_sporadic_task_model` | `periodic_task_respects_sporadic_task_model_correspondence` | [view](3_printed_declarations/periodic_task_respects_sporadic_task_model.md) |
| `valid_periods_are_valid_inter_arrival_times` | Remark | `Prosa.Model.Task.Arrival.PeriodicAsSporadic.valid_periods_are_valid_inter_arrival_times` | `valid_periods_are_valid_inter_arrival_times_correspondence` | [view](3_printed_declarations/valid_periods_are_valid_inter_arrival_times.md) |
| `periodic_task_sets_respect_sporadic_task_model` | Remark | `Prosa.Model.Task.Arrival.PeriodicAsSporadic.periodic_task_sets_respect_sporadic_task_model` | `periodic_task_sets_respect_sporadic_task_model_correspondence` | [view](3_printed_declarations/periodic_task_sets_respect_sporadic_task_model.md) |

## Certificates

| Module | Role |
|---|---|
| [`PeriodicAsSporadicCorrespondence`](4_correspondence/PeriodicAsSporadicCorrespondence.v) | Correspondences for `model/task/arrival/periodic_as_sporadic.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
