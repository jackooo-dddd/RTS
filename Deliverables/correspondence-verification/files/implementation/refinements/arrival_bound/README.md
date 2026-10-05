# `implementation/refinements/arrival_bound.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_arrivals_bound_T` | Inductive | `Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T` | `task_arrivals_bound_T_source_total, task_arrivals_bound_T_target_total` | [view](3_printed_declarations/task_arrivals_bound_T.md) |
| `taskab_eqdef_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.taskab_eqdef_T` | `taskab_eqdef_T_correspondence` | [view](3_printed_declarations/taskab_eqdef_T.md) |
| `horizon_of_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.horizon_of_T` | `horizon_of_T_correspondence` | [view](3_printed_declarations/horizon_of_T.md) |
| `steps_of_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.steps_of_T` | `steps_of_T_correspondence` | [view](3_printed_declarations/steps_of_T.md) |
| `time_steps_of_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.time_steps_of_T` | `time_steps_of_T_correspondence` | [view](3_printed_declarations/time_steps_of_T.md) |
| `step_at_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.step_at_T` | `step_at_T_correspondence` | [view](3_printed_declarations/step_at_T.md) |
| `value_at_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.value_at_T` | `value_at_T_correspondence` | [view](3_printed_declarations/value_at_T.md) |
| `extrapolated_arrival_curve_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.extrapolated_arrival_curve_T` | `extrapolated_arrival_curve_T_correspondence` | [view](3_printed_declarations/extrapolated_arrival_curve_T.md) |
| `ltn_steps_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.ltn_steps_T` | `ltn_steps_T_correspondence` | [view](3_printed_declarations/ltn_steps_T.md) |
| `sorted_ltn_steps_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.sorted_ltn_steps_T` | `sorted_ltn_steps_T_correspondence` | [view](3_printed_declarations/sorted_ltn_steps_T.md) |
| `leq_steps_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T` | `leq_steps_T_correspondence` | [view](3_printed_declarations/leq_steps_T.md) |
| `positive_horizon_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.positive_horizon_T` | `positive_horizon_T_correspondence` | [view](3_printed_declarations/positive_horizon_T.md) |
| `large_horizon_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.large_horizon_T` | `large_horizon_T_correspondence` | [view](3_printed_declarations/large_horizon_T.md) |
| `no_inf_arrivals_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.no_inf_arrivals_T` | `no_inf_arrivals_T_correspondence` | [view](3_printed_declarations/no_inf_arrivals_T.md) |
| `specified_bursts_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.specified_bursts_T` | `specified_bursts_T_correspondence` | [view](3_printed_declarations/specified_bursts_T.md) |
| `valid_extrapolated_arrival_curve_T` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.valid_extrapolated_arrival_curve_T` | `valid_extrapolated_arrival_curve_T_correspondence` | [view](3_printed_declarations/valid_extrapolated_arrival_curve_T.md) |
| `ACPrefixT_to_ACPrefix` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.ACPrefixT_to_ACPrefix` | `ACPrefixT_to_ACPrefix_correspondence` | [view](3_printed_declarations/ACPrefixT_to_ACPrefix.md) |
| `RArrivalCurvePrefix` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.RArrivalCurvePrefix` | `RArrivalCurvePrefix_correspondence` | [view](3_printed_declarations/RArrivalCurvePrefix.md) |
| `ACPrefix_to_ACPrefixT` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.ACPrefix_to_ACPrefixT` | `ACPrefix_to_ACPrefixT_correspondence` | [view](3_printed_declarations/ACPrefix_to_ACPrefixT.md) |
| `task_abT_to_task_ab` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.task_abT_to_task_ab` | `task_abT_to_task_ab_correspondence` | [view](3_printed_declarations/task_abT_to_task_ab.md) |
| `Rtask_ab` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab` | `Rtask_ab_correspondence` | [view](3_printed_declarations/Rtask_ab.md) |
| `task_ab_to_task_abT` | Definition | `Prosa.Implementation.Refinements.ArrivalBound.task_ab_to_task_abT` | `task_ab_to_task_abT_correspondence` | [view](3_printed_declarations/task_ab_to_task_abT.md) |
| `leq_stepsT_is_transitive` | Lemma | `Prosa.Implementation.Refinements.ArrivalBound.leq_stepsT_is_transitive` | `leq_stepsT_is_transitive_correspondence` | [view](3_printed_declarations/leq_stepsT_is_transitive.md) |
| `ltn_stepsT_is_transitive` | Lemma | `Prosa.Implementation.Refinements.ArrivalBound.ltn_stepsT_is_transitive` | `ltn_stepsT_is_transitive_correspondence` | [view](3_printed_declarations/ltn_stepsT_is_transitive.md) |
| `refine_leq_steps` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.refine_leq_steps` | `refine_leq_steps_correspondence` | [view](3_printed_declarations/refine_leq_steps.md) |
| `refine_ltn_steps` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.refine_ltn_steps` | `refine_ltn_steps_correspondence` | [view](3_printed_declarations/refine_ltn_steps.md) |
| `refine_ltn_steps_sorted` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.refine_ltn_steps_sorted` | `refine_ltn_steps_sorted_correspondence` | [view](3_printed_declarations/refine_ltn_steps_sorted.md) |
| `refine_leq_steps_sorted` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.refine_leq_steps_sorted` | `refine_leq_steps_sorted_correspondence` | [view](3_printed_declarations/refine_leq_steps_sorted.md) |
| `refine_value_at` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.refine_value_at` | `refine_value_at_correspondence` | [view](3_printed_declarations/refine_value_at.md) |
| `refine_get_time_steps` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.refine_get_time_steps` | `refine_get_time_steps_correspondence` | [view](3_printed_declarations/refine_get_time_steps.md) |
| `refine_arrival_curve_prefix` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.refine_arrival_curve_prefix` | `refine_arrival_curve_prefix_correspondence` | [view](3_printed_declarations/refine_arrival_curve_prefix.md) |
| `refine_ArrivalPrefix` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.refine_ArrivalPrefix` | `refine_ArrivalPrefix_correspondence` | [view](3_printed_declarations/refine_ArrivalPrefix.md) |
| `eq_listN` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.eq_listN` | `eq_listN_correspondence` | [view](3_printed_declarations/eq_listN.md) |
| `eq_NlistNN` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.eq_NlistNN` | `eq_NlistNN_correspondence` | [view](3_printed_declarations/eq_NlistNN.md) |
| `eq_taskab` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.eq_taskab` | `eq_taskab_correspondence` | [view](3_printed_declarations/eq_taskab.md) |
| `refine_task_ab_eq` | Instance | `Prosa.Implementation.Refinements.ArrivalBound.refine_task_ab_eq` | `refine_task_ab_eq_correspondence` | [view](3_printed_declarations/refine_task_ab_eq.md) |

## Certificates

| Module | Role |
|---|---|
| [`RabBase`](4_correspondence/RabBase.v) | Correspondences for `implementation/refinements/refinements.v`. |
| [`RefArrivalBoundCorrespondence`](4_correspondence/RefArrivalBoundCorrespondence.v) | Correspondences for `implementation/refinements/arrival_bound.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
