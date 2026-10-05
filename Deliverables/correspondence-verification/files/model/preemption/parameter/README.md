# `model/preemption/parameter.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `JobPreemptable` | Class | `Prosa.Model.Preemption.Parameter.JobPreemptable` | `JobPreemptable_source_total, JobPreemptable_target_total` | [view](3_printed_declarations/JobPreemptable.md) |
| `job_preemption_points` | Definition | `Prosa.Model.Preemption.Parameter.job_preemption_points` | `job_preemption_points_correspondence` | [view](3_printed_declarations/job_preemption_points.md) |
| `conversion_preserves_equivalence` | Remark | `Prosa.Model.Preemption.Parameter.conversion_preserves_equivalence` | `conversion_preserves_equivalence_correspondence` | [view](3_printed_declarations/conversion_preserves_equivalence.md) |
| `lengths_of_segments` | Definition | `Prosa.Model.Preemption.Parameter.lengths_of_segments` | `lengths_of_segments_correspondence` | [view](3_printed_declarations/lengths_of_segments.md) |
| `job_max_nonpreemptive_segment` | Definition | `Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment` | `job_max_nonpreemptive_segment_correspondence` | [view](3_printed_declarations/job_max_nonpreemptive_segment.md) |
| `job_last_nonpreemptive_segment` | Definition | `Prosa.Model.Preemption.Parameter.job_last_nonpreemptive_segment` | `job_last_nonpreemptive_segment_correspondence` | [view](3_printed_declarations/job_last_nonpreemptive_segment.md) |
| `job_rtct` | Definition | `Prosa.Model.Preemption.Parameter.job_rtct` | `job_rtct_correspondence` | [view](3_printed_declarations/job_rtct.md) |
| `preempted_at` | Definition | `Prosa.Model.Preemption.Parameter.preempted_at` | `preempted_at_correspondence` | [view](3_printed_declarations/preempted_at.md) |
| `job_cannot_become_nonpreemptive_before_execution` | Definition | `Prosa.Model.Preemption.Parameter.job_cannot_become_nonpreemptive_before_execution` | `job_cannot_become_nonpreemptive_before_execution_correspondence` | [view](3_printed_declarations/job_cannot_become_nonpreemptive_before_execution.md) |
| `job_cannot_be_nonpreemptive_after_completion` | Definition | `Prosa.Model.Preemption.Parameter.job_cannot_be_nonpreemptive_after_completion` | `job_cannot_be_nonpreemptive_after_completion_correspondence` | [view](3_printed_declarations/job_cannot_be_nonpreemptive_after_completion.md) |
| `not_preemptive_implies_scheduled` | Definition | `Prosa.Model.Preemption.Parameter.not_preemptive_implies_scheduled` | `not_preemptive_implies_scheduled_correspondence` | [view](3_printed_declarations/not_preemptive_implies_scheduled.md) |
| `execution_starts_with_preemption_point` | Definition | `Prosa.Model.Preemption.Parameter.execution_starts_with_preemption_point` | `execution_starts_with_preemption_point_correspondence` | [view](3_printed_declarations/execution_starts_with_preemption_point.md) |
| `valid_preemption_model` | Definition | `Prosa.Model.Preemption.Parameter.valid_preemption_model` | `valid_preemption_model_correspondence` | [view](3_printed_declarations/valid_preemption_model.md) |
| `no_superfluous_preemptions` | Definition | `Prosa.Model.Preemption.Parameter.no_superfluous_preemptions` | `no_superfluous_preemptions_correspondence` | [view](3_printed_declarations/no_superfluous_preemptions.md) |

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
