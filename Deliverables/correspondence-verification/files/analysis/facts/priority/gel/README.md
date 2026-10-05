# `analysis/facts/priority/gel.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `hep_job_priority_point` | Fact | `Prosa.Analysis.Facts.Priority.Gel.hep_job_priority_point` | `hep_job_priority_point_correspondence` | [view](3_printed_declarations/hep_job_priority_point.md) |
| `hep_job_arrival_gel` | Fact | `Prosa.Analysis.Facts.Priority.Gel.hep_job_arrival_gel` | `hep_job_arrival_gel_correspondence` | [view](3_printed_declarations/hep_job_arrival_gel.md) |
| `hep_job_arrives_before` | Lemma | `Prosa.Analysis.Facts.Priority.Gel.hep_job_arrives_before` | `hep_job_arrives_before_correspondence` | [view](3_printed_declarations/hep_job_arrives_before.md) |
| `hep_job_arrives_after_zero` | Corollary | `Prosa.Analysis.Facts.Priority.Gel.hep_job_arrives_after_zero` | `hep_job_arrives_after_zero_correspondence` | [view](3_printed_declarations/hep_job_arrives_after_zero.md) |
| `GEL_respects_sequential_tasks` | Lemma | `Prosa.Analysis.Facts.Priority.Gel.GEL_respects_sequential_tasks` | `GEL_respects_sequential_tasks_correspondence` | [view](3_printed_declarations/GEL_respects_sequential_tasks.md) |
| `GEL_implies_sequential_tasks` | Lemma | `Prosa.Analysis.Facts.Priority.Gel.GEL_implies_sequential_tasks` | `GEL_implies_sequential_tasks_correspondence` | [view](3_printed_declarations/GEL_implies_sequential_tasks.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPriorityGelCorrespondence`](4_correspondence/FactsPriorityGelCorrespondence.v) | Statement correspondences for `analysis/facts/priority/gel.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
