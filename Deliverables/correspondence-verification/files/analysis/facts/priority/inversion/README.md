# `analysis/facts/priority/inversion.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `sched_itself_implies_no_priority_inversion` | Lemma | `Prosa.Analysis.Facts.Priority.Inversion.sched_itself_implies_no_priority_inversion` | `sched_itself_implies_no_priority_inversion_correspondence` | [view](3_printed_declarations/sched_itself_implies_no_priority_inversion.md) |
| `priority_inversion_scheduled_at` | Lemma | `Prosa.Analysis.Facts.Priority.Inversion.priority_inversion_scheduled_at` | `priority_inversion_scheduled_at_correspondence` | [view](3_printed_declarations/priority_inversion_scheduled_at.md) |
| `no_priority_inversion_when_idle` | Lemma | `Prosa.Analysis.Facts.Priority.Inversion.no_priority_inversion_when_idle` | `no_priority_inversion_when_idle_correspondence` | [view](3_printed_declarations/no_priority_inversion_when_idle.md) |
| `priority_inversion_hep_job` | Lemma | `Prosa.Analysis.Facts.Priority.Inversion.priority_inversion_hep_job` | `priority_inversion_hep_job_correspondence` | [view](3_printed_declarations/priority_inversion_hep_job.md) |
| `no_priority_inversion_when_hep_job_scheduled` | Corollary | `Prosa.Analysis.Facts.Priority.Inversion.no_priority_inversion_when_hep_job_scheduled` | `no_priority_inversion_when_hep_job_scheduled_correspondence` | [view](3_printed_declarations/no_priority_inversion_when_hep_job_scheduled.md) |
| `uni_priority_inversion_P` | Lemma | `Prosa.Analysis.Facts.Priority.Inversion.uni_priority_inversion_P` | `uni_priority_inversion_P_correspondence` | [view](3_printed_declarations/uni_priority_inversion_P.md) |
| `cumulative_priority_inversion_cat` | Lemma | `Prosa.Analysis.Facts.Priority.Inversion.cumulative_priority_inversion_cat` | `cumulative_priority_inversion_cat_correspondence` | [view](3_printed_declarations/cumulative_priority_inversion_cat.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPriorityInversionCorrespondence`](4_correspondence/FactsPriorityInversionCorrespondence.v) | Statement correspondences for `analysis/facts/priority/inversion.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
