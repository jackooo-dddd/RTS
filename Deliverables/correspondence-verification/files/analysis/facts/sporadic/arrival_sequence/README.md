# `analysis/facts/sporadic/arrival_sequence.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `size_task_arrivals_at_leq_one` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.size_task_arrivals_at_leq_one` | `size_task_arrivals_at_leq_one_correspondence` | [view](3_printed_declarations/size_task_arrivals_at_leq_one.md) |
| `only_j_in_task_arrivals_at_j` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.only_j_in_task_arrivals_at_j` | `only_j_in_task_arrivals_at_j_correspondence` | [view](3_printed_declarations/only_j_in_task_arrivals_at_j.md) |
| `only_j_at_job_arrival_j` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.only_j_at_job_arrival_j` | `only_j_at_job_arrival_j_correspondence` | [view](3_printed_declarations/only_j_at_job_arrival_j.md) |
| `index_j_in_task_arrivals_at` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.index_j_in_task_arrivals_at` | `index_j_in_task_arrivals_at_correspondence` | [view](3_printed_declarations/index_j_in_task_arrivals_at.md) |
| `prev_job_arr_lt` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.prev_job_arr_lt` | `prev_job_arr_lt_correspondence` | [view](3_printed_declarations/prev_job_arr_lt.md) |
| `task_arrivals_at_as_task_arrivals_between` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.task_arrivals_at_as_task_arrivals_between` | `task_arrivals_at_as_task_arrivals_between_correspondence` | [view](3_printed_declarations/task_arrivals_at_as_task_arrivals_between.md) |
| `prev_job_cat` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.prev_job_cat` | `prev_job_cat_correspondence` | [view](3_printed_declarations/prev_job_cat.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsSporadicArrivalSequenceCorrespondence`](4_correspondence/FactsSporadicArrivalSequenceCorrespondence.v) | Statement correspondences for `analysis/facts/sporadic/arrival_sequence.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
