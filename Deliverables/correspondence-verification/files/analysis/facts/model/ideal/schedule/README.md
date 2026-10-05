# `analysis/facts/model/ideal/schedule.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `ideal_proc_model_is_a_uniprocessor_model` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_is_a_uniprocessor_model` | `ideal_proc_model_is_a_uniprocessor_model_correspondence` | [view](3_printed_declarations/ideal_proc_model_is_a_uniprocessor_model.md) |
| `service_in_service_on` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_in_service_on` | `service_in_service_on_correspondence` | [view](3_printed_declarations/service_in_service_on.md) |
| `service_in_def` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_in_def` | `service_in_def_correspondence` | [view](3_printed_declarations/service_in_def.md) |
| `ideal_proc_model_ensures_ideal_progress` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_ensures_ideal_progress` | `ideal_proc_model_ensures_ideal_progress_correspondence` | [view](3_printed_declarations/ideal_proc_model_ensures_ideal_progress.md) |
| `ideal_proc_model_provides_unit_service` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_provides_unit_service` | `ideal_proc_model_provides_unit_service_correspondence` | [view](3_printed_declarations/ideal_proc_model_provides_unit_service.md) |
| `ideal_proc_model_provides_unit_supply` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_provides_unit_supply` | `ideal_proc_model_provides_unit_supply_correspondence` | [view](3_printed_declarations/ideal_proc_model_provides_unit_supply.md) |
| `scheduled_in_def` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.scheduled_in_def` | `scheduled_in_def_correspondence` | [view](3_printed_declarations/scheduled_in_def.md) |
| `scheduled_at_def` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.scheduled_at_def` | `scheduled_at_def_correspondence` | [view](3_printed_declarations/scheduled_at_def.md) |
| `service_on_def` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_on_def` | `service_on_def_correspondence` | [view](3_printed_declarations/service_on_def.md) |
| `service_at_def` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_at_def` | `service_at_def_correspondence` | [view](3_printed_declarations/service_at_def.md) |
| `service_in_is_scheduled_in` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_in_is_scheduled_in` | `service_in_is_scheduled_in_correspondence` | [view](3_printed_declarations/service_in_is_scheduled_in.md) |
| `service_at_is_scheduled_at` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.service_at_is_scheduled_at` | `service_at_is_scheduled_at_correspondence` | [view](3_printed_declarations/service_at_is_scheduled_at.md) |
| `ideal_proc_model_fully_consuming` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_fully_consuming` | `ideal_proc_model_fully_consuming_correspondence` | [view](3_printed_declarations/ideal_proc_model_fully_consuming.md) |
| `ideal_proc_has_supply` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_has_supply` | `ideal_proc_has_supply_correspondence` | [view](3_printed_declarations/ideal_proc_has_supply.md) |
| `ideal_proc_model_sched_case_analysis` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_proc_model_sched_case_analysis` | `ideal_proc_model_sched_case_analysis_correspondence` | [view](3_printed_declarations/ideal_proc_model_sched_case_analysis.md) |
| `ideal_sched_implies_not_idle` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_sched_implies_not_idle` | `ideal_sched_implies_not_idle_correspondence` | [view](3_printed_declarations/ideal_sched_implies_not_idle.md) |
| `ideal_not_idle_implies_sched` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.ideal_not_idle_implies_sched` | `ideal_not_idle_implies_sched_correspondence` | [view](3_printed_declarations/ideal_not_idle_implies_sched.md) |
| `scheduled_job_at_def` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.scheduled_job_at_def` | `scheduled_job_at_def_correspondence` | [view](3_printed_declarations/scheduled_job_at_def.md) |
| `is_idle_def` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.Schedule.is_idle_def` | `is_idle_def_correspondence` | [view](3_printed_declarations/is_idle_def.md) |

## Certificates

| Module | Role |
|---|---|
| [`IdealScheduleCorrespondence`](4_correspondence/IdealScheduleCorrespondence.v) | Statement correspondences for `analysis/facts/model/ideal/schedule.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
