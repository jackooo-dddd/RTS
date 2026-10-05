# `analysis/facts/priority/edf.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `hep_job_deadline` | Fact | `Prosa.Analysis.Facts.Priority.Edf.hep_job_deadline` | `hep_job_deadline_correspondence` | [view](3_printed_declarations/hep_job_deadline.md) |
| `hep_job_task_deadline` | Fact | `Prosa.Analysis.Facts.Priority.Edf.hep_job_task_deadline` | `hep_job_task_deadline_correspondence` | [view](3_printed_declarations/hep_job_task_deadline.md) |
| `hep_job_arrival_edf` | Fact | `Prosa.Analysis.Facts.Priority.Edf.hep_job_arrival_edf` | `hep_job_arrival_edf_correspondence` | [view](3_printed_declarations/hep_job_arrival_edf.md) |
| `EDF_respects_sequential_tasks` | Lemma | `Prosa.Analysis.Facts.Priority.Edf.EDF_respects_sequential_tasks` | `EDF_respects_sequential_tasks_correspondence` | [view](3_printed_declarations/EDF_respects_sequential_tasks.md) |
| `EDF_implies_sequential_tasks` | Lemma | `Prosa.Analysis.Facts.Priority.Edf.EDF_implies_sequential_tasks` | `EDF_implies_sequential_tasks_correspondence` | [view](3_printed_declarations/EDF_implies_sequential_tasks.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPriorityEdfCorrespondence`](4_correspondence/FactsPriorityEdfCorrespondence.v) | Statement correspondences for `analysis/facts/priority/edf.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
