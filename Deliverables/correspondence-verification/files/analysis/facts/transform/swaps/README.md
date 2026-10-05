# `analysis/facts/transform/swaps.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `trivial_swap` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.trivial_swap` | `trivial_swap_correspondence` | [view](3_printed_declarations/trivial_swap.md) |
| `trivial_swap_service_invariant` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.trivial_swap_service_invariant` | `trivial_swap_service_invariant_correspondence` | [view](3_printed_declarations/trivial_swap_service_invariant.md) |
| `swap_other_times_invariant` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swap_other_times_invariant` | `swap_other_times_invariant_correspondence` | [view](3_printed_declarations/swap_other_times_invariant.md) |
| `swap_job_scheduled_t1` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_t1` | `swap_job_scheduled_t1_correspondence` | [view](3_printed_declarations/swap_job_scheduled_t1.md) |
| `swap_job_scheduled_t2` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_t2` | `swap_job_scheduled_t2_correspondence` | [view](3_printed_declarations/swap_job_scheduled_t2.md) |
| `swap_job_scheduled_other_times` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_other_times` | `swap_job_scheduled_other_times_correspondence` | [view](3_printed_declarations/swap_job_scheduled_other_times.md) |
| `swap_job_scheduled_cases` | Corollary | `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_cases` | `swap_job_scheduled_cases_correspondence` | [view](3_printed_declarations/swap_job_scheduled_cases.md) |
| `swap_job_scheduled` | Corollary | `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled` | `swap_job_scheduled_correspondence` | [view](3_printed_declarations/swap_job_scheduled.md) |
| `swap_job_scheduled_original_cases` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_original_cases` | `swap_job_scheduled_original_cases_correspondence` | [view](3_printed_declarations/swap_job_scheduled_original_cases.md) |
| `swap_job_scheduled_original` | Corollary | `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_original` | `swap_job_scheduled_original_correspondence` | [view](3_printed_declarations/swap_job_scheduled_original.md) |
| `swap_before_invariant` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swap_before_invariant` | `swap_before_invariant_correspondence` | [view](3_printed_declarations/swap_before_invariant.md) |
| `swap_after_invariant` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swap_after_invariant` | `swap_after_invariant_correspondence` | [view](3_printed_declarations/swap_after_invariant.md) |
| `service_before_swap_invariant` | Corollary | `Prosa.Analysis.Facts.Transform.Swaps.service_before_swap_invariant` | `service_before_swap_invariant_correspondence` | [view](3_printed_declarations/service_before_swap_invariant.md) |
| `service_after_swap_invariant` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.service_after_swap_invariant` | `service_after_swap_invariant_correspondence` | [view](3_printed_declarations/service_after_swap_invariant.md) |
| `service_of_others_invariant` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.service_of_others_invariant` | `service_of_others_invariant_correspondence` | [view](3_printed_declarations/service_of_others_invariant.md) |
| `swapped_service_bound` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swapped_service_bound` | `swapped_service_bound_correspondence` | [view](3_printed_declarations/swapped_service_bound.md) |
| `swapped_completed_jobs_dont_execute` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swapped_completed_jobs_dont_execute` | `swapped_completed_jobs_dont_execute_correspondence` | [view](3_printed_declarations/swapped_completed_jobs_dont_execute.md) |
| `swapped_jobs_come_from_arrival_sequence` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.swapped_jobs_come_from_arrival_sequence` | `swapped_jobs_come_from_arrival_sequence_correspondence` | [view](3_printed_declarations/swapped_jobs_come_from_arrival_sequence.md) |
| `uninvolved_implies_deadline_met` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.uninvolved_implies_deadline_met` | `uninvolved_implies_deadline_met_correspondence` | [view](3_printed_declarations/uninvolved_implies_deadline_met.md) |
| `moved_earlier_implies_deadline_met` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.moved_earlier_implies_deadline_met` | `moved_earlier_implies_deadline_met_correspondence` | [view](3_printed_declarations/moved_earlier_implies_deadline_met.md) |
| `moved_later_implies_deadline_met` | Lemma | `Prosa.Analysis.Facts.Transform.Swaps.moved_later_implies_deadline_met` | `moved_later_implies_deadline_met_correspondence` | [view](3_printed_declarations/moved_later_implies_deadline_met.md) |
| `edf_swap_no_deadline_misses_introduced` | Theorem | `Prosa.Analysis.Facts.Transform.Swaps.edf_swap_no_deadline_misses_introduced` | `edf_swap_no_deadline_misses_introduced_correspondence` | [view](3_printed_declarations/edf_swap_no_deadline_misses_introduced.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsSwapsCorrespondence`](4_correspondence/FactsSwapsCorrespondence.v) | Statement correspondences for `analysis/facts/transform/swaps.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
