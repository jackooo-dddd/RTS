# `implementation/refinements/arrival_curve.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `get_horizon_of_task` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task` | `get_horizon_of_task_correspondence` | [view](3_printed_declarations/get_horizon_of_task.md) |
| `get_time_steps_of_task` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task` | `get_time_steps_of_task_correspondence` | [view](3_printed_declarations/get_time_steps_of_task.md) |
| `time_steps_with_offset` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.time_steps_with_offset` | `time_steps_with_offset_correspondence` | [view](3_printed_declarations/time_steps_with_offset.md) |
| `repeat_steps_with_offset` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.repeat_steps_with_offset` | `repeat_steps_with_offset_correspondence` | [view](3_printed_declarations/repeat_steps_with_offset.md) |
| `task_rbf` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.task_rbf` | `task_rbf_correspondence` | [view](3_printed_declarations/task_rbf.md) |
| `valid_arrivals` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.valid_arrivals` | `valid_arrivals_correspondence` | [view](3_printed_declarations/valid_arrivals.md) |
| `is_periodic_arrivals` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.is_periodic_arrivals` | `is_periodic_arrivals_correspondence` | [view](3_printed_declarations/is_periodic_arrivals.md) |
| `is_sporadic_arrivals` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.is_sporadic_arrivals` | `is_sporadic_arrivals_correspondence` | [view](3_printed_declarations/is_sporadic_arrivals.md) |
| `is_etamax_arrivals` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.is_etamax_arrivals` | `is_etamax_arrivals_correspondence` | [view](3_printed_declarations/is_etamax_arrivals.md) |
| `has_valid_arrival_curve_prefix` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.has_valid_arrival_curve_prefix` | `has_valid_arrival_curve_prefix_correspondence` | [view](3_printed_declarations/has_valid_arrival_curve_prefix.md) |
| `task_set_with_valid_arrivals` | Definition | `Prosa.Implementation.Refinements.ArrivalCurve.task_set_with_valid_arrivals` | `task_set_with_valid_arrivals_correspondence` | [view](3_printed_declarations/task_set_with_valid_arrivals.md) |
| `arrival_cases` | Lemma | `Prosa.Implementation.Refinements.ArrivalCurve.arrival_cases` | `arrival_cases_correspondence` | [view](3_printed_declarations/arrival_cases.md) |
| `refine_valid_arrivals` | Instance | `Prosa.Implementation.Refinements.ArrivalCurve.refine_valid_arrivals` | `refine_valid_arrivals_correspondence` | [view](3_printed_declarations/refine_valid_arrivals.md) |
| `refine_repeat_steps_with_offset` | Instance | `Prosa.Implementation.Refinements.ArrivalCurve.refine_repeat_steps_with_offset` | `refine_repeat_steps_with_offset_correspondence` | [view](3_printed_declarations/refine_repeat_steps_with_offset.md) |
| `refine_get_horizon_of_task` | Instance | `Prosa.Implementation.Refinements.ArrivalCurve.refine_get_horizon_of_task` | `refine_get_horizon_of_task_correspondence` | [view](3_printed_declarations/refine_get_horizon_of_task.md) |
| `refine_ConcreteMaxArrivals'` | Instance | `Prosa.Implementation.Refinements.ArrivalCurve.refine_ConcreteMaxArrivals'` | `refine_ConcreteMaxArrivals'_correspondence` | [view](3_printed_declarations/refine_ConcreteMaxArrivals'.md) |
| `refine_get_arrival_curve_prefix` | Instance | `Prosa.Implementation.Refinements.ArrivalCurve.refine_get_arrival_curve_prefix` | `refine_get_arrival_curve_prefix_correspondence` | [view](3_printed_declarations/refine_get_arrival_curve_prefix.md) |
| `refine_get_arrival_curve_prefix'` | Instance | `Prosa.Implementation.Refinements.ArrivalCurve.refine_get_arrival_curve_prefix'` | `refine_get_arrival_curve_prefix'_correspondence` | [view](3_printed_declarations/refine_get_arrival_curve_prefix'.md) |
| `refine_sorted_leq_steps` | Instance | `Prosa.Implementation.Refinements.ArrivalCurve.refine_sorted_leq_steps` | `refine_sorted_leq_steps_correspondence` | [view](3_printed_declarations/refine_sorted_leq_steps.md) |
| `refine_task_rbf` | Instance | `Prosa.Implementation.Refinements.ArrivalCurve.refine_task_rbf` | `refine_task_rbf_correspondence` | [view](3_printed_declarations/refine_task_rbf.md) |

## Certificates

| Module | Role |
|---|---|
| [`RacBase`](4_correspondence/RacBase.v) | Correspondences for `implementation/refinements/refinements.v`. |
| [`RefArrivalCurveCorrespondence`](4_correspondence/RefArrivalCurveCorrespondence.v) | Correspondences for `implementation/refinements/arrival_curve.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
