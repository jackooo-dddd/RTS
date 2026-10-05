# `analysis/definitions/schedulability.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_response_time_bound` | Definition | `Prosa.Analysis.Definitions.Schedulability.task_response_time_bound` | `task_response_time_bound_correspondence` | [view](3_printed_declarations/task_response_time_bound.md) |
| `schedulable_task` | Definition | `Prosa.Analysis.Definitions.Schedulability.schedulable_task` | `schedulable_task_correspondence` | [view](3_printed_declarations/schedulable_task.md) |
| `schedulability_from_response_time_bound` | Lemma | `Prosa.Analysis.Definitions.Schedulability.schedulability_from_response_time_bound` | `schedulability_from_response_time_bound_correspondence` | [view](3_printed_declarations/schedulability_from_response_time_bound.md) |
| `all_deadlines_met` | Definition | `Prosa.Analysis.Definitions.Schedulability.all_deadlines_met` | `all_deadlines_met_correspondence` | [view](3_printed_declarations/all_deadlines_met.md) |
| `all_deadlines_of_arrivals_met` | Definition | `Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met` | `all_deadlines_of_arrivals_met_correspondence` | [view](3_printed_declarations/all_deadlines_of_arrivals_met.md) |
| `all_deadlines_met_in_valid_schedule` | Lemma | `Prosa.Analysis.Definitions.Schedulability.all_deadlines_met_in_valid_schedule` | `all_deadlines_met_in_valid_schedule_correspondence` | [view](3_printed_declarations/all_deadlines_met_in_valid_schedule.md) |

## Certificates

| Module | Role |
|---|---|
| [`SchedulabilityCorrespondence`](4_correspondence/SchedulabilityCorrespondence.v) | Certificates for `analysis/definitions/schedulability.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
