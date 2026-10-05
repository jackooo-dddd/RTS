# `analysis/facts/delay_propagation.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `consistent_propagated_arrival_sequence` | Lemma | `Prosa.Analysis.Facts.DelayPropagation.consistent_propagated_arrival_sequence` | `consistent_propagated_arrival_sequence_correspondence` | [view](3_printed_declarations/consistent_propagated_arrival_sequence.md) |
| `propagated_arrival_sequence_uniq` | Lemma | `Prosa.Analysis.Facts.DelayPropagation.propagated_arrival_sequence_uniq` | `propagated_arrival_sequence_uniq_correspondence` | [view](3_printed_declarations/propagated_arrival_sequence_uniq.md) |
| `valid_propagated_arrival_sequence` | Corollary | `Prosa.Analysis.Facts.DelayPropagation.valid_propagated_arrival_sequence` | `valid_propagated_arrival_sequence_correspondence` | [view](3_printed_declarations/valid_propagated_arrival_sequence.md) |
| `arrives_in_propagated_if` | Lemma | `Prosa.Analysis.Facts.DelayPropagation.arrives_in_propagated_if` | `arrives_in_propagated_if_correspondence` | [view](3_printed_declarations/arrives_in_propagated_if.md) |
| `arrives_in_propagated_only_if` | Lemma | `Prosa.Analysis.Facts.DelayPropagation.arrives_in_propagated_only_if` | `arrives_in_propagated_only_if_correspondence` | [view](3_printed_declarations/arrives_in_propagated_only_if.md) |
| `propagated_arrival_curve_valid` | Lemma | `Prosa.Analysis.Facts.DelayPropagation.propagated_arrival_curve_valid` | `propagated_arrival_curve_valid_correspondence` | [view](3_printed_declarations/propagated_arrival_curve_valid.md) |
| `trigger_job_arrival_bounded` | Lemma | `Prosa.Analysis.Facts.DelayPropagation.trigger_job_arrival_bounded` | `trigger_job_arrival_bounded_correspondence` | [view](3_printed_declarations/trigger_job_arrival_bounded.md) |
| `subset_trigger_jobs` | Lemma | `Prosa.Analysis.Facts.DelayPropagation.subset_trigger_jobs` | `subset_trigger_jobs_correspondence` | [view](3_printed_declarations/subset_trigger_jobs.md) |
| `job1_of_inj` | Lemma | `Prosa.Analysis.Facts.DelayPropagation.job1_of_inj` | `job1_of_inj_correspondence` | [view](3_printed_declarations/job1_of_inj.md) |
| `uniq_trigger_jobs` | Lemma | `Prosa.Analysis.Facts.DelayPropagation.uniq_trigger_jobs` | `uniq_trigger_jobs_correspondence` | [view](3_printed_declarations/uniq_trigger_jobs.md) |
| `trigger_job_size` | Corollary | `Prosa.Analysis.Facts.DelayPropagation.trigger_job_size` | `trigger_job_size_correspondence` | [view](3_printed_declarations/trigger_job_size.md) |
| `propagated_arrival_curve_respected` | Theorem | `Prosa.Analysis.Facts.DelayPropagation.propagated_arrival_curve_respected` | `propagated_arrival_curve_respected_correspondence` | [view](3_printed_declarations/propagated_arrival_curve_respected.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsDelayPropagationCorrespondence`](4_correspondence/FactsDelayPropagationCorrespondence.v) | Statement correspondences for `analysis/facts/delay_propagation.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
