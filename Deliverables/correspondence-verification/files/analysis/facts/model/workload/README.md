# `analysis/facts/model/workload.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `workload_of_jobs_filter` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_filter` | `workload_of_jobs_filter_correspondence` | [view](3_printed_declarations/workload_of_jobs_filter.md) |
| `workload_of_jobs_weaken` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_weaken` | `workload_of_jobs_weaken_correspondence` | [view](3_printed_declarations/workload_of_jobs_weaken.md) |
| `workload_of_jobs0` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs0` | `workload_of_jobs0_correspondence` | [view](3_printed_declarations/workload_of_jobs0.md) |
| `workload_of_jobs_le_sum_over_partitions` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_le_sum_over_partitions` | `workload_of_jobs_le_sum_over_partitions_correspondence` | [view](3_printed_declarations/workload_of_jobs_le_sum_over_partitions.md) |
| `workload_of_jobs_partitioned_by_tasks` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_partitioned_by_tasks` | `workload_of_jobs_partitioned_by_tasks_correspondence` | [view](3_printed_declarations/workload_of_jobs_partitioned_by_tasks.md) |
| `workload_of_other_jobs_split` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_other_jobs_split` | `workload_of_other_jobs_split_correspondence` | [view](3_printed_declarations/workload_of_other_jobs_split.md) |
| `workload_of_jobs_pred0` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_pred0` | `workload_of_jobs_pred0_correspondence` | [view](3_printed_declarations/workload_of_jobs_pred0.md) |
| `workload_of_jobs_case_on_pred` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_case_on_pred` | `workload_of_jobs_case_on_pred_correspondence` | [view](3_printed_declarations/workload_of_jobs_case_on_pred.md) |
| `workload_of_jobs_equiv_pred` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_equiv_pred` | `workload_of_jobs_equiv_pred_correspondence` | [view](3_printed_declarations/workload_of_jobs_equiv_pred.md) |
| `workload_of_job_eq_job_arrival` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_job_eq_job_arrival` | `workload_of_job_eq_job_arrival_correspondence` | [view](3_printed_declarations/workload_of_job_eq_job_arrival.md) |
| `workload_job_and_ahep_eq_workload_hep` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_job_and_ahep_eq_workload_hep` | `workload_job_and_ahep_eq_workload_hep_correspondence` | [view](3_printed_declarations/workload_job_and_ahep_eq_workload_hep.md) |
| `workload_of_jobs_nil_tail` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_nil_tail` | `workload_of_jobs_nil_tail_correspondence` | [view](3_printed_declarations/workload_of_jobs_nil_tail.md) |
| `workload_of_jobs_cat` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_cat` | `workload_of_jobs_cat_correspondence` | [view](3_printed_declarations/workload_of_jobs_cat.md) |
| `workload_of_jobs_reduce_range` | Corollary | `Prosa.Analysis.Facts.Model.Workload.workload_of_jobs_reduce_range` | `workload_of_jobs_reduce_range_correspondence` | [view](3_printed_declarations/workload_of_jobs_reduce_range.md) |
| `workload_minus_job_cost'` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_minus_job_cost'` | `workload_minus_job_cost'_correspondence` | [view](3_printed_declarations/workload_minus_job_cost'.md) |
| `workload_minus_job_cost` | Corollary | `Prosa.Analysis.Facts.Model.Workload.workload_minus_job_cost` | `workload_minus_job_cost_correspondence` | [view](3_printed_declarations/workload_minus_job_cost.md) |
| `workload_equal_subset` | Lemma | `Prosa.Analysis.Facts.Model.Workload.workload_equal_subset` | `workload_equal_subset_correspondence` | [view](3_printed_declarations/workload_equal_subset.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsWorkloadCorrespondence`](4_correspondence/FactsWorkloadCorrespondence.v) | Statement correspondences for `analysis/facts/model/workload.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
