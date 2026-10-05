# `analysis/facts/model/overheads/schedule_change_bound.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `schedule_changes_bounded_by_total_arrivals_JLFP` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound.schedule_changes_bounded_by_total_arrivals_JLFP` | `schedule_changes_bounded_by_total_arrivals_JLFP_correspondence` | [view](3_printed_declarations/schedule_changes_bounded_by_total_arrivals_JLFP.md) |
| `schedule_changes_bounded_by_total_arrivals_FP` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound.schedule_changes_bounded_by_total_arrivals_FP` | `schedule_changes_bounded_by_total_arrivals_FP_correspondence` | [view](3_printed_declarations/schedule_changes_bounded_by_total_arrivals_FP.md) |
| `schedule_changes_bounded_by_total_arrivals_FIFO` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.ScheduleChangeBound.schedule_changes_bounded_by_total_arrivals_FIFO` | `schedule_changes_bounded_by_total_arrivals_FIFO_correspondence` | [view](3_printed_declarations/schedule_changes_bounded_by_total_arrivals_FIFO.md) |

## Certificates

| Module | Role |
|---|---|
| [`OverheadsScheduleChangeBoundCorrespondence`](4_correspondence/OverheadsScheduleChangeBoundCorrespondence.v) | Statement correspondences for `analysis/facts/model/overheads/schedule_change_bound.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
