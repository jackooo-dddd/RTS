# `analysis/facts/model/overheads/schedule_change.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `number_schedule_changes_cat` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.number_schedule_changes_cat` | `number_schedule_changes_cat_correspondence` | [view](3_printed_declarations/number_schedule_changes_cat.md) |
| `first_schedule_change_exists` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.first_schedule_change_exists` | `first_schedule_change_exists_correspondence` | [view](3_printed_declarations/first_schedule_change_exists.md) |
| `number_schedule_changes_widen` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.number_schedule_changes_widen` | `number_schedule_changes_widen_correspondence` | [view](3_printed_declarations/number_schedule_changes_widen.md) |
| `same_scheduled_state_merge` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.same_scheduled_state_merge` | `same_scheduled_state_merge_correspondence` | [view](3_printed_declarations/same_scheduled_state_merge.md) |
| `no_schedule_changes_implies_constant_schedule` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.no_schedule_changes_implies_constant_schedule` | `no_schedule_changes_implies_constant_schedule_correspondence` | [view](3_printed_declarations/no_schedule_changes_implies_constant_schedule.md) |
| `no_changes_implies_same_scheduled_job` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.ScheduleChange.no_changes_implies_same_scheduled_job` | `no_changes_implies_same_scheduled_job_correspondence` | [view](3_printed_declarations/no_changes_implies_same_scheduled_job.md) |

## Certificates

| Module | Role |
|---|---|
| [`OverheadsScheduleChangeFactsCorrespondence`](4_correspondence/OverheadsScheduleChangeFactsCorrespondence.v) | Statement correspondences for `analysis/facts/model/overheads/schedule_change.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
