# `model/preemption/limited_preemptive.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `JobPreemptionPoints` | Class | `Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints` | `JobPreemptionPoints_source_total, JobPreemptionPoints_target_total` | [view](3_printed_declarations/JobPreemptionPoints.md) |
| `beginning_of_execution_in_preemption_points` | Definition | `Prosa.Model.Preemption.LimitedPreemptive.beginning_of_execution_in_preemption_points` | `beginning_of_execution_in_preemption_points_correspondence` | [view](3_printed_declarations/beginning_of_execution_in_preemption_points.md) |
| `end_of_execution_in_preemption_points` | Definition | `Prosa.Model.Preemption.LimitedPreemptive.end_of_execution_in_preemption_points` | `end_of_execution_in_preemption_points_correspondence` | [view](3_printed_declarations/end_of_execution_in_preemption_points.md) |
| `preemption_points_is_nondecreasing_sequence` | Definition | `Prosa.Model.Preemption.LimitedPreemptive.preemption_points_is_nondecreasing_sequence` | `preemption_points_is_nondecreasing_sequence_correspondence` | [view](3_printed_declarations/preemption_points_is_nondecreasing_sequence.md) |
| `valid_limited_preemptions_job_model` | Definition | `Prosa.Model.Preemption.LimitedPreemptive.valid_limited_preemptions_job_model` | `valid_limited_preemptions_job_model_correspondence` | [view](3_printed_declarations/valid_limited_preemptions_job_model.md) |

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
