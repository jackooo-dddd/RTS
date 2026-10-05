# `analysis/facts/busy_interval/carry_in.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `no_carry_in_at_zero` | Lemma | `Prosa.Analysis.Facts.BusyInterval.CarryIn.no_carry_in_at_zero` | `no_carry_in_at_zero_correspondence` | [view](3_printed_declarations/no_carry_in_at_zero.md) |
| `pending_job_not_idle` | Lemma | `Prosa.Analysis.Facts.BusyInterval.CarryIn.pending_job_not_idle` | `pending_job_not_idle_correspondence` | [view](3_printed_declarations/pending_job_not_idle.md) |
| `idle_instant_no_carry_in` | Lemma | `Prosa.Analysis.Facts.BusyInterval.CarryIn.idle_instant_no_carry_in` | `idle_instant_no_carry_in_correspondence` | [view](3_printed_declarations/idle_instant_no_carry_in.md) |
| `idle_instant_next_no_carry_in` | Lemma | `Prosa.Analysis.Facts.BusyInterval.CarryIn.idle_instant_next_no_carry_in` | `idle_instant_next_no_carry_in_correspondence` | [view](3_printed_declarations/idle_instant_next_no_carry_in.md) |
| `total_service_is_bounded_by_Δ` | Lemma | `Prosa.Analysis.Facts.BusyInterval.CarryIn.total_service_is_bounded_by_Δ` | `total_service_is_bounded_by_Δ_correspondence` | [view](3_printed_declarations/total_service_is_bounded_by_Δ.md) |
| `low_total_service_implies_existence_of_time_with_no_carry_in` | Lemma | `Prosa.Analysis.Facts.BusyInterval.CarryIn.low_total_service_implies_existence_of_time_with_no_carry_in` | `low_total_service_implies_existence_of_time_with_no_carry_in_correspondence` | [view](3_printed_declarations/low_total_service_implies_existence_of_time_with_no_carry_in.md) |
| `completion_of_all_jobs_implies_no_carry_in` | Lemma | `Prosa.Analysis.Facts.BusyInterval.CarryIn.completion_of_all_jobs_implies_no_carry_in` | `completion_of_all_jobs_implies_no_carry_in_correspondence` | [view](3_printed_declarations/completion_of_all_jobs_implies_no_carry_in.md) |
| `processor_is_not_too_busy` | Lemma | `Prosa.Analysis.Facts.BusyInterval.CarryIn.processor_is_not_too_busy` | `processor_is_not_too_busy_correspondence` | [view](3_printed_declarations/processor_is_not_too_busy.md) |
| `busy_interval_from_total_workload_bound` | Theorem | `Prosa.Analysis.Facts.BusyInterval.CarryIn.busy_interval_from_total_workload_bound` | `busy_interval_from_total_workload_bound_correspondence` | [view](3_printed_declarations/busy_interval_from_total_workload_bound.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsCarryInCorrespondence`](4_correspondence/FactsCarryInCorrespondence.v) | Statement correspondence for `analysis/facts/busy_interval/carry_in.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
