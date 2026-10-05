# `analysis/facts/completes_at.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `scheduled_at_precedes_completes_at` | Lemma | `Prosa.Analysis.Facts.CompletesAt.scheduled_at_precedes_completes_at` | `scheduled_at_precedes_completes_at_correspondence` | [view](3_printed_declarations/scheduled_at_precedes_completes_at.md) |
| `job_completes_at_most_once` | Lemma | `Prosa.Analysis.Facts.CompletesAt.job_completes_at_most_once` | `job_completes_at_most_once_correspondence` | [view](3_printed_declarations/job_completes_at_most_once.md) |
| `only_one_job_completes_at_a_time` | Lemma | `Prosa.Analysis.Facts.CompletesAt.only_one_job_completes_at_a_time` | `only_one_job_completes_at_a_time_correspondence` | [view](3_printed_declarations/only_one_job_completes_at_a_time.md) |
| `completetion_time_is_preemption_time` | Lemma | `Prosa.Analysis.Facts.CompletesAt.completetion_time_is_preemption_time` | `completetion_time_is_preemption_time_correspondence` | [view](3_printed_declarations/completetion_time_is_preemption_time.md) |
| `no_early_hep_job_completes_during_busy_prefix` | Lemma | `Prosa.Analysis.Facts.CompletesAt.no_early_hep_job_completes_during_busy_prefix` | `no_early_hep_job_completes_during_busy_prefix_correspondence` | [view](3_printed_declarations/no_early_hep_job_completes_during_busy_prefix.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsCompletesAtCorrespondence`](4_correspondence/FactsCompletesAtCorrespondence.v) | Statement correspondences for `analysis/facts/completes_at.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
