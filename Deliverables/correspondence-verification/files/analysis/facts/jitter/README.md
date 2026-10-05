# `analysis/facts/jitter.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `jitter_arrives_in_iff` | Corollary | `Prosa.Analysis.Facts.Jitter.jitter_arrives_in_iff` | `jitter_arrives_in_iff_correspondence` | [view](3_printed_declarations/jitter_arrives_in_iff.md) |
| `valid_release_sequence` | Corollary | `Prosa.Analysis.Facts.Jitter.valid_release_sequence` | `valid_release_sequence_correspondence` | [view](3_printed_declarations/valid_release_sequence.md) |
| `valid_release_curve` | Corollary | `Prosa.Analysis.Facts.Jitter.valid_release_curve` | `valid_release_curve_correspondence` | [view](3_printed_declarations/valid_release_curve.md) |
| `release_curve_respected` | Corollary | `Prosa.Analysis.Facts.Jitter.release_curve_respected` | `release_curve_respected_correspondence` | [view](3_printed_declarations/release_curve_respected.md) |
| `jitter_prop_same_jobs` | Lemma | `Prosa.Analysis.Facts.Jitter.jitter_prop_same_jobs` | `jitter_prop_same_jobs_correspondence` | [view](3_printed_declarations/jitter_prop_same_jobs.md) |
| `jitter_prop_same_jobs'` | Lemma | `Prosa.Analysis.Facts.Jitter.jitter_prop_same_jobs'` | `jitter_prop_same_jobs'_correspondence` | [view](3_printed_declarations/jitter_prop_same_jobs'.md) |
| `jitter_prop_valid_costs` | Lemma | `Prosa.Analysis.Facts.Jitter.jitter_prop_valid_costs` | `jitter_prop_valid_costs_correspondence` | [view](3_printed_declarations/jitter_prop_valid_costs.md) |
| `jitter_ready_to_execute` | Lemma | `Prosa.Analysis.Facts.Jitter.jitter_ready_to_execute` | `jitter_ready_to_execute_correspondence` | [view](3_printed_declarations/jitter_ready_to_execute.md) |
| `jitter_work_conservation` | Theorem | `Prosa.Analysis.Facts.Jitter.jitter_work_conservation` | `jitter_work_conservation_correspondence` | [view](3_printed_declarations/jitter_work_conservation.md) |
| `jitter_valid_schedule` | Lemma | `Prosa.Analysis.Facts.Jitter.jitter_valid_schedule` | `jitter_valid_schedule_correspondence` | [view](3_printed_declarations/jitter_valid_schedule.md) |
| `jitter_scheduled_jobs_at_equiv` | Lemma | `Prosa.Analysis.Facts.Jitter.jitter_scheduled_jobs_at_equiv` | `jitter_scheduled_jobs_at_equiv_correspondence` | [view](3_printed_declarations/jitter_scheduled_jobs_at_equiv.md) |
| `jitter_scheduled_job_at_eq` | Lemma | `Prosa.Analysis.Facts.Jitter.jitter_scheduled_job_at_eq` | `jitter_scheduled_job_at_eq_correspondence` | [view](3_printed_declarations/jitter_scheduled_job_at_eq.md) |
| `jitter_FP_compliance` | Theorem | `Prosa.Analysis.Facts.Jitter.jitter_FP_compliance` | `jitter_FP_compliance_correspondence` | [view](3_printed_declarations/jitter_FP_compliance.md) |
| `jitter_response_time_bound` | Theorem | `Prosa.Analysis.Facts.Jitter.jitter_response_time_bound` | `jitter_response_time_bound_correspondence` | [view](3_printed_declarations/jitter_response_time_bound.md) |

## Certificates

| Module | Role |
|---|---|
| [`JitterCorrespondence`](4_correspondence/JitterCorrespondence.v) | Statement correspondences for `analysis/facts/jitter.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
