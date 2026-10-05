# `analysis/facts/job_index.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `case_arrival_lte_implies_equal_job` | Lemma | `Prosa.Analysis.Facts.JobIndex.case_arrival_lte_implies_equal_job` | `case_arrival_lte_implies_equal_job_correspondence` | [view](3_printed_declarations/case_arrival_lte_implies_equal_job.md) |
| `case_arrival_gt_implies_equal_job` | Lemma | `Prosa.Analysis.Facts.JobIndex.case_arrival_gt_implies_equal_job` | `case_arrival_gt_implies_equal_job_correspondence` | [view](3_printed_declarations/case_arrival_gt_implies_equal_job.md) |
| `equal_index_implies_equal_jobs` | Lemma | `Prosa.Analysis.Facts.JobIndex.equal_index_implies_equal_jobs` | `equal_index_implies_equal_jobs_correspondence` | [view](3_printed_declarations/equal_index_implies_equal_jobs.md) |
| `diff_jobs_iff_diff_indices` | Lemma | `Prosa.Analysis.Facts.JobIndex.diff_jobs_iff_diff_indices` | `diff_jobs_iff_diff_indices_correspondence` | [view](3_printed_declarations/diff_jobs_iff_diff_indices.md) |
| `index_as_sum_size_and_index` | Lemma | `Prosa.Analysis.Facts.JobIndex.index_as_sum_size_and_index` | `index_as_sum_size_and_index_correspondence` | [view](3_printed_declarations/index_as_sum_size_and_index.md) |
| `arrival_lt_implies_job_in_arrivals_between_P` | Lemma | `Prosa.Analysis.Facts.JobIndex.arrival_lt_implies_job_in_arrivals_between_P` | `arrival_lt_implies_job_in_arrivals_between_P_correspondence` | [view](3_printed_declarations/arrival_lt_implies_job_in_arrivals_between_P.md) |
| `index_lte_implies_arrival_lte_P` | Lemma | `Prosa.Analysis.Facts.JobIndex.index_lte_implies_arrival_lte_P` | `index_lte_implies_arrival_lte_P_correspondence` | [view](3_printed_declarations/index_lte_implies_arrival_lte_P.md) |
| `job_index_same_in_task_arrivals` | Lemma | `Prosa.Analysis.Facts.JobIndex.job_index_same_in_task_arrivals` | `job_index_same_in_task_arrivals_correspondence` | [view](3_printed_declarations/job_index_same_in_task_arrivals.md) |
| `index_job_lt_size_task_arrivals_up_to_job` | Lemma | `Prosa.Analysis.Facts.JobIndex.index_job_lt_size_task_arrivals_up_to_job` | `index_job_lt_size_task_arrivals_up_to_job_correspondence` | [view](3_printed_declarations/index_job_lt_size_task_arrivals_up_to_job.md) |
| `index_lte_implies_arrival_lte` | Lemma | `Prosa.Analysis.Facts.JobIndex.index_lte_implies_arrival_lte` | `index_lte_implies_arrival_lte_correspondence` | [view](3_printed_declarations/index_lte_implies_arrival_lte.md) |
| `earlier_arrival_implies_lower_index` | Lemma | `Prosa.Analysis.Facts.JobIndex.earlier_arrival_implies_lower_index` | `earlier_arrival_implies_lower_index_correspondence` | [view](3_printed_declarations/earlier_arrival_implies_lower_index.md) |
| `job_index_minus_one_lt_size_task_arrivals_up_to` | Lemma | `Prosa.Analysis.Facts.JobIndex.job_index_minus_one_lt_size_task_arrivals_up_to` | `job_index_minus_one_lt_size_task_arrivals_up_to_correspondence` | [view](3_printed_declarations/job_index_minus_one_lt_size_task_arrivals_up_to.md) |
| `positive_job_index_implies_positive_size_of_task_arrivals` | Lemma | `Prosa.Analysis.Facts.JobIndex.positive_job_index_implies_positive_size_of_task_arrivals` | `positive_job_index_implies_positive_size_of_task_arrivals_correspondence` | [view](3_printed_declarations/positive_job_index_implies_positive_size_of_task_arrivals.md) |
| `prev_job_arr` | Lemma | `Prosa.Analysis.Facts.JobIndex.prev_job_arr` | `prev_job_arr_correspondence` | [view](3_printed_declarations/prev_job_arr.md) |
| `prev_job_index` | Lemma | `Prosa.Analysis.Facts.JobIndex.prev_job_index` | `prev_job_index_correspondence` | [view](3_printed_declarations/prev_job_index.md) |
| `prev_job_task` | Lemma | `Prosa.Analysis.Facts.JobIndex.prev_job_task` | `prev_job_task_correspondence` | [view](3_printed_declarations/prev_job_task.md) |
| `prev_job_in_task_arrivals_up_to_j` | Lemma | `Prosa.Analysis.Facts.JobIndex.prev_job_in_task_arrivals_up_to_j` | `prev_job_in_task_arrivals_up_to_j_correspondence` | [view](3_printed_declarations/prev_job_in_task_arrivals_up_to_j.md) |
| `prev_job_arr_lte` | Lemma | `Prosa.Analysis.Facts.JobIndex.prev_job_arr_lte` | `prev_job_arr_lte_correspondence` | [view](3_printed_declarations/prev_job_arr_lte.md) |
| `prev_job_index_j` | Lemma | `Prosa.Analysis.Facts.JobIndex.prev_job_index_j` | `prev_job_index_j_correspondence` | [view](3_printed_declarations/prev_job_index_j.md) |
| `no_jobs_between_consecutive_jobs` | Lemma | `Prosa.Analysis.Facts.JobIndex.no_jobs_between_consecutive_jobs` | `no_jobs_between_consecutive_jobs_correspondence` | [view](3_printed_declarations/no_jobs_between_consecutive_jobs.md) |
| `exists_jobs_before_j` | Lemma | `Prosa.Analysis.Facts.JobIndex.exists_jobs_before_j` | `exists_jobs_before_j_correspondence` | [view](3_printed_declarations/exists_jobs_before_j.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsJobIndexCorrespondence`](4_correspondence/FactsJobIndexCorrespondence.v) | Statement correspondences for `analysis/facts/job_index.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
