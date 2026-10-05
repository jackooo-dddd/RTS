# `analysis/facts/model/scheduled.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `scheduled_jobs_at_iff` | Lemma | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_iff` | `scheduled_jobs_at_iff_correspondence` | [view](3_printed_declarations/scheduled_jobs_at_iff.md) |
| `scheduled_jobs_at_nil` | Lemma | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_nil` | `scheduled_jobs_at_nil_correspondence` | [view](3_printed_declarations/scheduled_jobs_at_nil.md) |
| `not_scheduled_when_idle` | Corollary | `Prosa.Analysis.Facts.Model.Scheduled.not_scheduled_when_idle` | `not_scheduled_when_idle_correspondence` | [view](3_printed_declarations/not_scheduled_when_idle.md) |
| `scheduled_at_implies_in_served_at` | Lemma | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_at_implies_in_served_at` | `scheduled_at_implies_in_served_at_correspondence` | [view](3_printed_declarations/scheduled_at_implies_in_served_at.md) |
| `scheduled_jobs_at_seq1` | Corollary | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_seq1` | `scheduled_jobs_at_seq1_correspondence` | [view](3_printed_declarations/scheduled_jobs_at_seq1.md) |
| `scheduled_jobs_at_uni_cases` | Corollary | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_uni_cases` | `scheduled_jobs_at_uni_cases_correspondence` | [view](3_printed_declarations/scheduled_jobs_at_uni_cases.md) |
| `scheduled_jobs_at_uni` | Lemma | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_uni` | `scheduled_jobs_at_uni_correspondence` | [view](3_printed_declarations/scheduled_jobs_at_uni.md) |
| `scheduled_job_at_scheduled_at` | Corollary | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_job_at_scheduled_at` | `scheduled_job_at_scheduled_at_correspondence` | [view](3_printed_declarations/scheduled_job_at_scheduled_at.md) |
| `scheduled_jobs_at_scheduled_at` | Corollary | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_jobs_at_scheduled_at` | `scheduled_jobs_at_scheduled_at_correspondence` | [view](3_printed_declarations/scheduled_jobs_at_scheduled_at.md) |
| `scheduled_job_at_none` | Corollary | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_job_at_none` | `scheduled_job_at_none_correspondence` | [view](3_printed_declarations/scheduled_job_at_none.md) |
| `is_idle_iff` | Corollary | `Prosa.Analysis.Facts.Model.Scheduled.is_idle_iff` | `is_idle_iff_correspondence` | [view](3_printed_declarations/is_idle_iff.md) |
| `is_nonidle_iff` | Corollary | `Prosa.Analysis.Facts.Model.Scheduled.is_nonidle_iff` | `is_nonidle_iff_correspondence` | [view](3_printed_declarations/is_nonidle_iff.md) |
| `scheduled_at_dec` | Lemma | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_at_dec` | `scheduled_at_dec_correspondence` | [view](3_printed_declarations/scheduled_at_dec.md) |
| `scheduled_at_cases` | Corollary | `Prosa.Analysis.Facts.Model.Scheduled.scheduled_at_cases` | `scheduled_at_cases_correspondence` | [view](3_printed_declarations/scheduled_at_cases.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsScheduledCorrespondence`](4_correspondence/FactsScheduledCorrespondence.v) | Statement correspondences for `analysis/facts/model/scheduled.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
