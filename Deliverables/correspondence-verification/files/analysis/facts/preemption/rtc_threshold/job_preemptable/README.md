# `analysis/facts/preemption/rtc_threshold/job_preemptable.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `preemption_points_of_zero_cost_job` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.preemption_points_of_zero_cost_job` | `preemption_points_of_zero_cost_job_correspondence` | [view](3_printed_declarations/preemption_points_of_zero_cost_job.md) |
| `zero_in_preemption_points` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.zero_in_preemption_points` | `zero_in_preemption_points_correspondence` | [view](3_printed_declarations/zero_in_preemption_points.md) |
| `job_cost_in_preemption_points` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_cost_in_preemption_points` | `job_cost_in_preemption_points_correspondence` | [view](3_printed_declarations/job_cost_in_preemption_points.md) |
| `size_of_preemption_points` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.size_of_preemption_points` | `size_of_preemption_points_correspondence` | [view](3_printed_declarations/size_of_preemption_points.md) |
| `preemption_points_nondecreasing` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.preemption_points_nondecreasing` | `preemption_points_nondecreasing_correspondence` | [view](3_printed_declarations/preemption_points_nondecreasing.md) |
| `job_cost_is_last_element_of_preemption_points` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_cost_is_last_element_of_preemption_points` | `job_cost_is_last_element_of_preemption_points_correspondence` | [view](3_printed_declarations/job_cost_is_last_element_of_preemption_points.md) |
| `job_last_nonpreemptive_segment_positive` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_last_nonpreemptive_segment_positive` | `job_last_nonpreemptive_segment_positive_correspondence` | [view](3_printed_declarations/job_last_nonpreemptive_segment_positive.md) |
| `job_max_nonpreemptive_segment_positive` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_max_nonpreemptive_segment_positive` | `job_max_nonpreemptive_segment_positive_correspondence` | [view](3_printed_declarations/job_max_nonpreemptive_segment_positive.md) |
| `job_max_nonpreemptive_segment_le_job_cost` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_max_nonpreemptive_segment_le_job_cost` | `job_max_nonpreemptive_segment_le_job_cost_correspondence` | [view](3_printed_declarations/job_max_nonpreemptive_segment_le_job_cost.md) |
| `job_last_nonpreemptive_segment_le_job_cost` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_last_nonpreemptive_segment_le_job_cost` | `job_last_nonpreemptive_segment_le_job_cost_correspondence` | [view](3_printed_declarations/job_last_nonpreemptive_segment_le_job_cost.md) |
| `job_run_to_completion_threshold_positive` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_run_to_completion_threshold_positive` | `job_run_to_completion_threshold_positive_correspondence` | [view](3_printed_declarations/job_run_to_completion_threshold_positive.md) |
| `job_run_to_completion_threshold_le_job_cost` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_run_to_completion_threshold_le_job_cost` | `job_run_to_completion_threshold_le_job_cost_correspondence` | [view](3_printed_declarations/job_run_to_completion_threshold_le_job_cost.md) |
| `job_cannot_be_preempted_within_last_segment` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_cannot_be_preempted_within_last_segment` | `job_cannot_be_preempted_within_last_segment_correspondence` | [view](3_printed_declarations/job_cannot_be_preempted_within_last_segment.md) |
| `job_nonpreemptive_after_run_to_completion_threshold` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_nonpreemptive_after_run_to_completion_threshold` | `job_nonpreemptive_after_run_to_completion_threshold_correspondence` | [view](3_printed_declarations/job_nonpreemptive_after_run_to_completion_threshold.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsRtcJobPreemptableCorrespondence`](4_correspondence/FactsRtcJobPreemptableCorrespondence.v) | Statement correspondences for `analysis/facts/preemption/rtc_threshold/job_preemptable.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
