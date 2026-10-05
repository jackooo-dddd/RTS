# `model/task/preemption/limited_preemptive.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_beginning_of_execution_in_preemption_points` | Definition | `Prosa.Model.Task.Preemption.LimitedPreemptive.task_beginning_of_execution_in_preemption_points` | `task_beginning_of_execution_in_preemption_points_correspondence` | [view](3_printed_declarations/task_beginning_of_execution_in_preemption_points.md) |
| `task_end_of_execution_in_preemption_points` | Definition | `Prosa.Model.Task.Preemption.LimitedPreemptive.task_end_of_execution_in_preemption_points` | `task_end_of_execution_in_preemption_points_correspondence` | [view](3_printed_declarations/task_end_of_execution_in_preemption_points.md) |
| `nondecreasing_task_preemption_points` | Definition | `Prosa.Model.Task.Preemption.LimitedPreemptive.nondecreasing_task_preemption_points` | `nondecreasing_task_preemption_points_correspondence` | [view](3_printed_declarations/nondecreasing_task_preemption_points.md) |
| `consistent_job_segment_count` | Definition | `Prosa.Model.Task.Preemption.LimitedPreemptive.consistent_job_segment_count` | `consistent_job_segment_count_correspondence` | [view](3_printed_declarations/consistent_job_segment_count.md) |
| `job_respects_segment_lengths` | Definition | `Prosa.Model.Task.Preemption.LimitedPreemptive.job_respects_segment_lengths` | `job_respects_segment_lengths_correspondence` | [view](3_printed_declarations/job_respects_segment_lengths.md) |
| `task_segments_are_nonempty` | Definition | `Prosa.Model.Task.Preemption.LimitedPreemptive.task_segments_are_nonempty` | `task_segments_are_nonempty_correspondence` | [view](3_printed_declarations/task_segments_are_nonempty.md) |
| `valid_fixed_preemption_points_task_model` | Definition | `Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_task_model` | `valid_fixed_preemption_points_task_model_correspondence` | [view](3_printed_declarations/valid_fixed_preemption_points_task_model.md) |
| `valid_fixed_preemption_points_model` | Definition | `Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_model` | `valid_fixed_preemption_points_model_correspondence` | [view](3_printed_declarations/valid_fixed_preemption_points_model.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
