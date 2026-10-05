# `analysis/facts/busy_interval/existence.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_completes_within_busy_interval` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.job_completes_within_busy_interval` | `job_completes_within_busy_interval_correspondence` | [view](3_printed_declarations/job_completes_within_busy_interval.md) |
| `not_quiet_implies_exists_pending_job` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.not_quiet_implies_exists_pending_job` | `not_quiet_implies_exists_pending_job_correspondence` | [view](3_printed_declarations/not_quiet_implies_exists_pending_job.md) |
| `idle_time_implies_quiet_time_at_the_next_time_instant` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.idle_time_implies_quiet_time_at_the_next_time_instant` | `idle_time_implies_quiet_time_at_the_next_time_instant_correspondence` | [view](3_printed_declarations/idle_time_implies_quiet_time_at_the_next_time_instant.md) |
| `pending_hp_job_exists` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.pending_hp_job_exists` | `pending_hp_job_exists_correspondence` | [view](3_printed_declarations/pending_hp_job_exists.md) |
| `not_quiet_implies_not_idle` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.not_quiet_implies_not_idle` | `not_quiet_implies_not_idle_correspondence` | [view](3_printed_declarations/not_quiet_implies_not_idle.md) |
| `hep_jobs_receive_no_service_before_quiet_time` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.hep_jobs_receive_no_service_before_quiet_time` | `hep_jobs_receive_no_service_before_quiet_time_correspondence` | [view](3_printed_declarations/hep_jobs_receive_no_service_before_quiet_time.md) |
| `no_idle_time_within_non_quiet_time_interval` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.no_idle_time_within_non_quiet_time_interval` | `no_idle_time_within_non_quiet_time_interval_correspondence` | [view](3_printed_declarations/no_idle_time_within_non_quiet_time_interval.md) |
| `exists_busy_interval_prefix` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.exists_busy_interval_prefix` | `exists_busy_interval_prefix_correspondence` | [view](3_printed_declarations/exists_busy_interval_prefix.md) |
| `busy_interval_has_uninterrupted_service` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.busy_interval_has_uninterrupted_service` | `busy_interval_has_uninterrupted_service_correspondence` | [view](3_printed_declarations/busy_interval_has_uninterrupted_service.md) |
| `busy_interval_too_much_workload` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.busy_interval_too_much_workload` | `busy_interval_too_much_workload_correspondence` | [view](3_printed_declarations/busy_interval_too_much_workload.md) |
| `busy_interval_workload_larger_than_interval` | Corollary | `Prosa.Analysis.Facts.BusyInterval.Existence.busy_interval_workload_larger_than_interval` | `busy_interval_workload_larger_than_interval_correspondence` | [view](3_printed_declarations/busy_interval_workload_larger_than_interval.md) |
| `busy_interval_is_bounded` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.busy_interval_is_bounded` | `busy_interval_is_bounded_correspondence` | [view](3_printed_declarations/busy_interval_is_bounded.md) |
| `exists_busy_interval` | Corollary | `Prosa.Analysis.Facts.BusyInterval.Existence.exists_busy_interval` | `exists_busy_interval_correspondence` | [view](3_printed_declarations/exists_busy_interval.md) |
| `busy_interval_bounds_response_time` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Existence.busy_interval_bounds_response_time` | `busy_interval_bounds_response_time_correspondence` | [view](3_printed_declarations/busy_interval_bounds_response_time.md) |

## Certificates

| Module | Role |
|---|---|
| [`ExistenceCorrespondence`](4_correspondence/ExistenceCorrespondence.v) | Statement correspondence for `analysis/facts/busy_interval/existence.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
