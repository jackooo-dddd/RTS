# `analysis/facts/model/overheads/blackout_bound.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `blackout_during_split` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.blackout_during_split` | `blackout_during_split_correspondence` | [view](3_printed_declarations/blackout_during_split.md) |
| `total_dispatch_time_eq_job_dispatch_time` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_dispatch_time_eq_job_dispatch_time` | `total_dispatch_time_eq_job_dispatch_time_correspondence` | [view](3_printed_declarations/total_dispatch_time_eq_job_dispatch_time.md) |
| `total_cswitch_time_eq_job_cswitch_time` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_cswitch_time_eq_job_cswitch_time` | `total_cswitch_time_eq_job_cswitch_time_correspondence` | [view](3_printed_declarations/total_cswitch_time_eq_job_cswitch_time.md) |
| `total_CRPD_time_eq_job_CRPD_time` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_CRPD_time_eq_job_CRPD_time` | `total_CRPD_time_eq_job_CRPD_time_correspondence` | [view](3_printed_declarations/total_CRPD_time_eq_job_CRPD_time.md) |
| `total_time_in_dispatch_is_bounded` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_time_in_dispatch_is_bounded` | `total_time_in_dispatch_is_bounded_correspondence` | [view](3_printed_declarations/total_time_in_dispatch_is_bounded.md) |
| `total_time_in_cswitch_is_bounded` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_time_in_cswitch_is_bounded` | `total_time_in_cswitch_is_bounded_correspondence` | [view](3_printed_declarations/total_time_in_cswitch_is_bounded.md) |
| `total_time_in_CRPD_is_bounded` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.total_time_in_CRPD_is_bounded` | `total_time_in_CRPD_is_bounded_correspondence` | [view](3_printed_declarations/total_time_in_CRPD_is_bounded.md) |
| `no_sched_changes_bounded_overheads_blackout` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.no_sched_changes_bounded_overheads_blackout` | `no_sched_changes_bounded_overheads_blackout_correspondence` | [view](3_printed_declarations/no_sched_changes_bounded_overheads_blackout.md) |
| `sched_changes_start_busy_pref_bounded_overheads_blackout` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.sched_changes_start_busy_pref_bounded_overheads_blackout` | `sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence` | [view](3_printed_declarations/sched_changes_start_busy_pref_bounded_overheads_blackout.md) |
| `fin_sched_changes_start_busy_pref_bounded_overheads_blackout` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.fin_sched_changes_start_busy_pref_bounded_overheads_blackout` | `fin_sched_changes_start_busy_pref_bounded_overheads_blackout_correspondence` | [view](3_printed_declarations/fin_sched_changes_start_busy_pref_bounded_overheads_blackout.md) |
| `finite_sched_changes_bounded_overheads_blackout` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.BlackoutBound.finite_sched_changes_bounded_overheads_blackout` | `finite_sched_changes_bounded_overheads_blackout_correspondence` | [view](3_printed_declarations/finite_sched_changes_bounded_overheads_blackout.md) |

## Certificates

| Module | Role |
|---|---|
| [`OverheadsBlackoutBoundCorrespondence`](4_correspondence/OverheadsBlackoutBoundCorrespondence.v) | Statement correspondences for `analysis/facts/model/overheads/blackout_bound.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
