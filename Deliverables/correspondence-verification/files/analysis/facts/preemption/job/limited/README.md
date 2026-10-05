# `analysis/facts/preemption/job/limited.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `zero_in_preemption_points` | Remark | `Prosa.Analysis.Facts.Preemption.Job.Limited.zero_in_preemption_points` | `zero_in_preemption_points_correspondence` | [view](3_printed_declarations/zero_in_preemption_points.md) |
| `zero_is_first_element` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Limited.zero_is_first_element` | `zero_is_first_element_correspondence` | [view](3_printed_declarations/zero_is_first_element.md) |
| `list_of_preemption_point_is_not_empty` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Limited.list_of_preemption_point_is_not_empty` | `list_of_preemption_point_is_not_empty_correspondence` | [view](3_printed_declarations/list_of_preemption_point_is_not_empty.md) |
| `job_cost_in_nonpreemptive_points` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Limited.job_cost_in_nonpreemptive_points` | `job_cost_in_nonpreemptive_points_correspondence` | [view](3_printed_declarations/job_cost_in_nonpreemptive_points.md) |
| `number_of_preemption_points_at_least_two` | Corollary | `Prosa.Analysis.Facts.Preemption.Job.Limited.number_of_preemption_points_at_least_two` | `number_of_preemption_points_at_least_two_correspondence` | [view](3_printed_declarations/number_of_preemption_points_at_least_two.md) |
| `antidensity_of_preemption_points` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Limited.antidensity_of_preemption_points` | `antidensity_of_preemption_points_correspondence` | [view](3_printed_declarations/antidensity_of_preemption_points.md) |
| `work_belongs_to_some_nonpreemptive_segment` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Limited.work_belongs_to_some_nonpreemptive_segment` | `work_belongs_to_some_nonpreemptive_segment_correspondence` | [view](3_printed_declarations/work_belongs_to_some_nonpreemptive_segment.md) |
| `job_parameters_last_np_to_job_limited` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Limited.job_parameters_last_np_to_job_limited` | `job_parameters_last_np_to_job_limited_correspondence` | [view](3_printed_declarations/job_parameters_last_np_to_job_limited.md) |
| `job_parameters_max_np_to_job_limited` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Limited.job_parameters_max_np_to_job_limited` | `job_parameters_max_np_to_job_limited_correspondence` | [view](3_printed_declarations/job_parameters_max_np_to_job_limited.md) |
| `valid_fixed_preemption_points_model_lemma` | Lemma | `Prosa.Analysis.Facts.Preemption.Job.Limited.valid_fixed_preemption_points_model_lemma` | `valid_fixed_preemption_points_model_lemma_correspondence` | [view](3_printed_declarations/valid_fixed_preemption_points_model_lemma.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsLimitedJobCorrespondence`](4_correspondence/FactsLimitedJobCorrespondence.v) | Statement correspondences for `analysis/facts/preemption/job/limited.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
