# `implementation/facts/maximal_arrival_sequence.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `arr_seq_is_a_set` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.arr_seq_is_a_set` | `arr_seq_is_a_set_correspondence` | [view](3_printed_declarations/arr_seq_is_a_set.md) |
| `concrete_all_jobs_from_taskset` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.concrete_all_jobs_from_taskset` | `concrete_all_jobs_from_taskset_correspondence` | [view](3_printed_declarations/concrete_all_jobs_from_taskset.md) |
| `arrival_times_are_consistent` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.arrival_times_are_consistent` | `arrival_times_are_consistent_correspondence` | [view](3_printed_declarations/arrival_times_are_consistent.md) |
| `concrete_valid_job_cost` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.concrete_valid_job_cost` | `concrete_valid_job_cost_correspondence` | [view](3_printed_declarations/concrete_valid_job_cost.md) |
| `task_arrivals_at_eq_generate_jobs_at` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.task_arrivals_at_eq_generate_jobs_at` | `task_arrivals_at_eq_generate_jobs_at_correspondence` | [view](3_printed_declarations/task_arrivals_at_eq_generate_jobs_at.md) |
| `task_arrivals_at_eq` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.task_arrivals_at_eq` | `task_arrivals_at_eq_correspondence` | [view](3_printed_declarations/task_arrivals_at_eq.md) |
| `number_of_task_arrivals_eq` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.number_of_task_arrivals_eq` | `number_of_task_arrivals_eq_correspondence` | [view](3_printed_declarations/number_of_task_arrivals_eq.md) |
| `extend_horizon_size` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.extend_horizon_size` | `extend_horizon_size_correspondence` | [view](3_printed_declarations/extend_horizon_size.md) |
| `prefix_up_to_size` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.prefix_up_to_size` | `prefix_up_to_size_correspondence` | [view](3_printed_declarations/prefix_up_to_size.md) |
| `n_arrivals_at_prefix_inclusion1` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.n_arrivals_at_prefix_inclusion1` | `n_arrivals_at_prefix_inclusion1_correspondence` | [view](3_printed_declarations/n_arrivals_at_prefix_inclusion1.md) |
| `n_arrivals_at_prefix_inclusion` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.n_arrivals_at_prefix_inclusion` | `n_arrivals_at_prefix_inclusion_correspondence` | [view](3_printed_declarations/n_arrivals_at_prefix_inclusion.md) |
| `max_arrivals_at_next_max_arrivals_eq` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.max_arrivals_at_next_max_arrivals_eq` | `max_arrivals_at_next_max_arrivals_eq_correspondence` | [view](3_printed_declarations/max_arrivals_at_next_max_arrivals_eq.md) |
| `n_arrivals_at_leq` | Lemma | `Prosa.Implementation.Facts.MaximalArrivalSequence.n_arrivals_at_leq` | `n_arrivals_at_leq_correspondence` | [view](3_printed_declarations/n_arrivals_at_leq.md) |
| `concrete_is_arrival_curve` | Theorem | `Prosa.Implementation.Facts.MaximalArrivalSequence.concrete_is_arrival_curve` | `concrete_is_arrival_curve_correspondence` | [view](3_printed_declarations/concrete_is_arrival_curve.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsMaximalArrivalSequenceCorrespondence`](4_correspondence/FactsMaximalArrivalSequenceCorrespondence.v) | Statement correspondences for `implementation/facts/maximal_arrival_sequence.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
