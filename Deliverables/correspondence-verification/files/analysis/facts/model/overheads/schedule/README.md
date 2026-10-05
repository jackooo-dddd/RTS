# `analysis/facts/model/overheads/schedule.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `overheads_proc_model_is_a_uniprocessor_model` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_is_a_uniprocessor_model` | `overheads_proc_model_is_a_uniprocessor_model_correspondence` | [view](3_printed_declarations/overheads_proc_model_is_a_uniprocessor_model.md) |
| `overheads_proc_model_provides_unit_supply` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_provides_unit_supply` | `overheads_proc_model_provides_unit_supply_correspondence` | [view](3_printed_declarations/overheads_proc_model_provides_unit_supply.md) |
| `overheads_proc_model_fully_consuming` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.Schedule.overheads_proc_model_fully_consuming` | `overheads_proc_model_fully_consuming_correspondence` | [view](3_printed_declarations/overheads_proc_model_fully_consuming.md) |
| `scheduled_job_dec` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_job_dec` | `scheduled_job_dec_correspondence` | [view](3_printed_declarations/scheduled_job_dec.md) |
| `scheduled_at_iff_scheduled_job` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.Schedule.scheduled_at_iff_scheduled_job` | `scheduled_at_iff_scheduled_job_correspondence` | [view](3_printed_declarations/scheduled_at_iff_scheduled_job.md) |
| `job_scheduled_in_busy_interval_prefix` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.Schedule.job_scheduled_in_busy_interval_prefix` | `job_scheduled_in_busy_interval_prefix_correspondence` | [view](3_printed_declarations/job_scheduled_in_busy_interval_prefix.md) |

## Certificates

| Module | Role |
|---|---|
| [`OverheadsScheduleCorrespondence`](4_correspondence/OverheadsScheduleCorrespondence.v) | Statement correspondences for `analysis/facts/model/overheads/schedule.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
