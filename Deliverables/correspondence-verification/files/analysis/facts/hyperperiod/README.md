# `analysis/facts/hyperperiod.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `hyperperiod_int_mult_of_any_task` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.hyperperiod_int_mult_of_any_task` | `hyperperiod_int_mult_of_any_task_correspondence` | [view](3_printed_declarations/hyperperiod_int_mult_of_any_task.md) |
| `valid_periods_imply_pos_hp` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.valid_periods_imply_pos_hp` | `valid_periods_imply_pos_hp_correspondence` | [view](3_printed_declarations/valid_periods_imply_pos_hp.md) |
| `corresponding_jobs_have_same_task` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.corresponding_jobs_have_same_task` | `corresponding_jobs_have_same_task_correspondence` | [view](3_printed_declarations/corresponding_jobs_have_same_task.md) |
| `all_jobs_arrive_within_hyperperiod` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.all_jobs_arrive_within_hyperperiod` | `all_jobs_arrive_within_hyperperiod_correspondence` | [view](3_printed_declarations/all_jobs_arrive_within_hyperperiod.md) |
| `eq_size_hyp_lt` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.eq_size_hyp_lt` | `eq_size_hyp_lt_correspondence` | [view](3_printed_declarations/eq_size_hyp_lt.md) |
| `eq_size_of_arrivals_in_hyperperiod` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.eq_size_of_arrivals_in_hyperperiod` | `eq_size_of_arrivals_in_hyperperiod_correspondence` | [view](3_printed_declarations/eq_size_of_arrivals_in_hyperperiod.md) |
| `job_in_hp_arrives_in_task_arrivals_up_to` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.job_in_hp_arrives_in_task_arrivals_up_to` | `job_in_hp_arrives_in_task_arrivals_up_to_correspondence` | [view](3_printed_declarations/job_in_hp_arrives_in_task_arrivals_up_to.md) |
| `job_in_own_hp` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.job_in_own_hp` | `job_in_own_hp_correspondence` | [view](3_printed_declarations/job_in_own_hp.md) |
| `corr_job_in_task_arrivals_up_to` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.corr_job_in_task_arrivals_up_to` | `corr_job_in_task_arrivals_up_to_correspondence` | [view](3_printed_declarations/corr_job_in_task_arrivals_up_to.md) |
| `corresponding_job_arrives` | Lemma | `Prosa.Analysis.Facts.Hyperperiod.corresponding_job_arrives` | `corresponding_job_arrives_correspondence` | [view](3_printed_declarations/corresponding_job_arrives.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsHyperperiodCorrespondence`](4_correspondence/FactsHyperperiodCorrespondence.v) | Statement correspondences for `analysis/facts/hyperperiod.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
