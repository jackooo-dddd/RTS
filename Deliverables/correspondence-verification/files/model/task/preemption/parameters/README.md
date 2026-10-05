# `model/task/preemption/parameters.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `TaskMaxNonpreemptiveSegment` | Class | `Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment` | `TaskMaxNonpreemptiveSegment_source_total, TaskMaxNonpreemptiveSegment_target_total` | [view](3_printed_declarations/TaskMaxNonpreemptiveSegment.md) |
| `TaskRunToCompletionThreshold` | Class | `Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold` | `TaskRunToCompletionThreshold_source_total, TaskRunToCompletionThreshold_target_total` | [view](3_printed_declarations/TaskRunToCompletionThreshold.md) |
| `TaskPreemptionPoints` | Class | `Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints` | `TaskPreemptionPoints_source_total, TaskPreemptionPoints_target_total` | [view](3_printed_declarations/TaskPreemptionPoints.md) |
| `task_max_nonpr_segment` | Definition | `Prosa.Model.Task.Preemption.Parameters.task_max_nonpr_segment` | `task_max_nonpr_segment_correspondence` | [view](3_printed_declarations/task_max_nonpr_segment.md) |
| `task_last_nonpr_segment` | Definition | `Prosa.Model.Task.Preemption.Parameters.task_last_nonpr_segment` | `task_last_nonpr_segment_correspondence` | [view](3_printed_declarations/task_last_nonpr_segment.md) |
| `TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion` | Instance | `Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion` | `TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion_correspondence` | [view](3_printed_declarations/TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion.md) |
| `job_respects_max_nonpreemptive_segment` | Definition | `Prosa.Model.Task.Preemption.Parameters.job_respects_max_nonpreemptive_segment` | `job_respects_max_nonpreemptive_segment_correspondence` | [view](3_printed_declarations/job_respects_max_nonpreemptive_segment.md) |
| `nonpreemptive_regions_have_bounded_length` | Definition | `Prosa.Model.Task.Preemption.Parameters.nonpreemptive_regions_have_bounded_length` | `nonpreemptive_regions_have_bounded_length_correspondence` | [view](3_printed_declarations/nonpreemptive_regions_have_bounded_length.md) |
| `model_with_bounded_nonpreemptive_segments` | Definition | `Prosa.Model.Task.Preemption.Parameters.model_with_bounded_nonpreemptive_segments` | `model_with_bounded_nonpreemptive_segments_correspondence` | [view](3_printed_declarations/model_with_bounded_nonpreemptive_segments.md) |
| `valid_model_with_bounded_nonpreemptive_segments` | Definition | `Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments` | `valid_model_with_bounded_nonpreemptive_segments_correspondence` | [view](3_printed_declarations/valid_model_with_bounded_nonpreemptive_segments.md) |
| `task_rtc_bounded_by_cost` | Definition | `Prosa.Model.Task.Preemption.Parameters.task_rtc_bounded_by_cost` | `task_rtc_bounded_by_cost_correspondence` | [view](3_printed_declarations/task_rtc_bounded_by_cost.md) |
| `job_respects_task_rtc` | Definition | `Prosa.Model.Task.Preemption.Parameters.job_respects_task_rtc` | `job_respects_task_rtc_correspondence` | [view](3_printed_declarations/job_respects_task_rtc.md) |
| `valid_task_run_to_completion_threshold` | Definition | `Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold` | `valid_task_run_to_completion_threshold_correspondence` | [view](3_printed_declarations/valid_task_run_to_completion_threshold.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
