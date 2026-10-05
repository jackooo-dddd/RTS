# `analysis/facts/model/dbf.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_arrivals_with_deadline_within_eq` | Lemma | `Prosa.Analysis.Facts.Model.Dbf.task_arrivals_with_deadline_within_eq` | `task_arrivals_with_deadline_within_eq_correspondence` | [view](3_printed_declarations/task_arrivals_with_deadline_within_eq.md) |
| `num_task_arrivals_with_deadline_within_eq` | Corollary | `Prosa.Analysis.Facts.Model.Dbf.num_task_arrivals_with_deadline_within_eq` | `num_task_arrivals_with_deadline_within_eq_correspondence` | [view](3_printed_declarations/num_task_arrivals_with_deadline_within_eq.md) |
| `task_demand_within` | Definition | `Prosa.Analysis.Facts.Model.Dbf.task_demand_within` | `task_demand_within_correspondence` | [view](3_printed_declarations/task_demand_within.md) |
| `task_demand_within_le_task_dbf` | Lemma | `Prosa.Analysis.Facts.Model.Dbf.task_demand_within_le_task_dbf` | `task_demand_within_le_task_dbf_correspondence` | [view](3_printed_declarations/task_demand_within_le_task_dbf.md) |
| `task_demand_within_le_task_rbf_shifted` | Corollary | `Prosa.Analysis.Facts.Model.Dbf.task_demand_within_le_task_rbf_shifted` | `task_demand_within_le_task_rbf_shifted_correspondence` | [view](3_printed_declarations/task_demand_within_le_task_rbf_shifted.md) |
| `total_demand_within` | Definition | `Prosa.Analysis.Facts.Model.Dbf.total_demand_within` | `total_demand_within_correspondence` | [view](3_printed_declarations/total_demand_within.md) |
| `total_demand_within_le_total_dbf` | Lemma | `Prosa.Analysis.Facts.Model.Dbf.total_demand_within_le_total_dbf` | `total_demand_within_le_total_dbf_correspondence` | [view](3_printed_declarations/total_demand_within_le_total_dbf.md) |
| `total_demand_within_le_sum_task_rbf_shifted` | Corollary | `Prosa.Analysis.Facts.Model.Dbf.total_demand_within_le_sum_task_rbf_shifted` | `total_demand_within_le_sum_task_rbf_shifted_correspondence` | [view](3_printed_declarations/total_demand_within_le_sum_task_rbf_shifted.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsDbfCorrespondence`](4_correspondence/FactsDbfCorrespondence.v) | Correspondences for `analysis/facts/model/dbf.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
