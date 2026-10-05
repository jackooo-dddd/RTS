# `analysis/abstract/busy_interval.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `busy_interval_prefix_case` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.busy_interval_prefix_case` | `busy_interval_prefix_case_correspondence` | [view](3_printed_declarations/busy_interval_prefix_case.md) |
| `terminating_busy_prefix_is_busy_interval` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.terminating_busy_prefix_is_busy_interval` | `terminating_busy_prefix_is_busy_interval_correspondence` | [view](3_printed_declarations/terminating_busy_prefix_is_busy_interval.md) |
| `job_completes_within_busy_interval` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.job_completes_within_busy_interval` | `job_completes_within_busy_interval_correspondence` | [view](3_printed_declarations/job_completes_within_busy_interval.md) |
| `no_service_before_busy_interval` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.no_service_before_busy_interval` | `no_service_before_busy_interval_correspondence` | [view](3_printed_declarations/no_service_before_busy_interval.md) |
| `service_within_busy_interval_ge_job_cost` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.service_within_busy_interval_ge_job_cost` | `service_within_busy_interval_ge_job_cost_correspondence` | [view](3_printed_declarations/service_within_busy_interval_ge_job_cost.md) |
| `abstract_busy_interval_arrivals_before` | Fact | `Prosa.Analysis.Abstract.BusyInterval.abstract_busy_interval_arrivals_before` | `abstract_busy_interval_arrivals_before_correspondence` | [view](3_printed_declarations/abstract_busy_interval_arrivals_before.md) |
| `abstract_busy_interval_prefix_job_arrival` | Fact | `Prosa.Analysis.Abstract.BusyInterval.abstract_busy_interval_prefix_job_arrival` | `abstract_busy_interval_prefix_job_arrival_correspondence` | [view](3_printed_declarations/abstract_busy_interval_prefix_job_arrival.md) |
| `abstract_busy_interval_job_arrival` | Fact | `Prosa.Analysis.Abstract.BusyInterval.abstract_busy_interval_job_arrival` | `abstract_busy_interval_job_arrival_correspondence` | [view](3_printed_declarations/abstract_busy_interval_job_arrival.md) |
| `service_and_interference_bound` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.service_and_interference_bound` | `service_and_interference_bound_correspondence` | [view](3_printed_declarations/service_and_interference_bound.md) |
| `exists_busy_interval_prefix` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.exists_busy_interval_prefix` | `exists_busy_interval_prefix_correspondence` | [view](3_printed_declarations/exists_busy_interval_prefix.md) |
| `busy_interval_has_uninterrupted_service` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.busy_interval_has_uninterrupted_service` | `busy_interval_has_uninterrupted_service_correspondence` | [view](3_printed_declarations/busy_interval_has_uninterrupted_service.md) |
| `busy_interval_too_much_workload` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.busy_interval_too_much_workload` | `busy_interval_too_much_workload_correspondence` | [view](3_printed_declarations/busy_interval_too_much_workload.md) |
| `t1δ_is_quiet` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.t1δ_is_quiet` | `t1δ_is_quiet_correspondence` | [view](3_printed_declarations/t1δ_is_quiet.md) |
| `t1δ_is_quiet_contra` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.t1δ_is_quiet_contra` | `t1δ_is_quiet_contra_correspondence` | [view](3_printed_declarations/t1δ_is_quiet_contra.md) |
| `busy_interval_is_bounded` | Lemma | `Prosa.Analysis.Abstract.BusyInterval.busy_interval_is_bounded` | `busy_interval_is_bounded_correspondence` | [view](3_printed_declarations/busy_interval_is_bounded.md) |

## Certificates

| Module | Role |
|---|---|
| [`BusyIntervalAbstractCorrespondence`](4_correspondence/BusyIntervalAbstractCorrespondence.v) | Statement correspondences for `analysis/abstract/busy_interval.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
