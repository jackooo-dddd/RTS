# `analysis/facts/busy_interval/hep_at_pt.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `instant_t_is_not_idle` | Lemma | `Prosa.Analysis.Facts.BusyInterval.HepAtPt.instant_t_is_not_idle` | `instant_t_is_not_idle_correspondence` | [view](3_printed_declarations/instant_t_is_not_idle.md) |
| `scheduled_at_preemption_time_implies_higher_or_equal_priority_lt` | Lemma | `Prosa.Analysis.Facts.BusyInterval.HepAtPt.scheduled_at_preemption_time_implies_higher_or_equal_priority_lt` | `scheduled_at_preemption_time_implies_higher_or_equal_priority_lt_correspondence` | [view](3_printed_declarations/scheduled_at_preemption_time_implies_higher_or_equal_priority_lt.md) |
| `scheduled_at_preemption_time_implies_higher_or_equal_priority_eq` | Lemma | `Prosa.Analysis.Facts.BusyInterval.HepAtPt.scheduled_at_preemption_time_implies_higher_or_equal_priority_eq` | `scheduled_at_preemption_time_implies_higher_or_equal_priority_eq_correspondence` | [view](3_printed_declarations/scheduled_at_preemption_time_implies_higher_or_equal_priority_eq.md) |
| `scheduled_at_preemption_time_implies_higher_or_equal_priority` | Corollary | `Prosa.Analysis.Facts.BusyInterval.HepAtPt.scheduled_at_preemption_time_implies_higher_or_equal_priority` | `scheduled_at_preemption_time_implies_higher_or_equal_priority_correspondence` | [view](3_printed_declarations/scheduled_at_preemption_time_implies_higher_or_equal_priority.md) |
| `scheduled_at_preemption_time_implies_arrived_between_within_busy_interval` | Lemma | `Prosa.Analysis.Facts.BusyInterval.HepAtPt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval` | `scheduled_at_preemption_time_implies_arrived_between_within_busy_interval_correspondence` | [view](3_printed_declarations/scheduled_at_preemption_time_implies_arrived_between_within_busy_interval.md) |
| `not_quiet_implies_exists_scheduled_hp_job_at_preemption_point` | Corollary | `Prosa.Analysis.Facts.BusyInterval.HepAtPt.not_quiet_implies_exists_scheduled_hp_job_at_preemption_point` | `not_quiet_implies_exists_scheduled_hp_job_at_preemption_point_correspondence` | [view](3_printed_declarations/not_quiet_implies_exists_scheduled_hp_job_at_preemption_point.md) |
| `not_quiet_implies_exists_scheduled_hp_job_after_preemption_point` | Lemma | `Prosa.Analysis.Facts.BusyInterval.HepAtPt.not_quiet_implies_exists_scheduled_hp_job_after_preemption_point` | `not_quiet_implies_exists_scheduled_hp_job_after_preemption_point_correspondence` | [view](3_printed_declarations/not_quiet_implies_exists_scheduled_hp_job_after_preemption_point.md) |
| `not_quiet_implies_exists_scheduled_hp_job` | Lemma | `Prosa.Analysis.Facts.BusyInterval.HepAtPt.not_quiet_implies_exists_scheduled_hp_job` | `not_quiet_implies_exists_scheduled_hp_job_correspondence` | [view](3_printed_declarations/not_quiet_implies_exists_scheduled_hp_job.md) |

## Certificates

| Module | Role |
|---|---|
| [`HepAtPtCorrespondence`](4_correspondence/HepAtPtCorrespondence.v) | Statement correspondence for `analysis/facts/busy_interval/hep_at_pt.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
