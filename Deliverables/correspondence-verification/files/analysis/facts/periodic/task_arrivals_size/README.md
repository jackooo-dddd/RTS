# `analysis/facts/periodic/task_arrivals_size.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_arrivals_size_at_non_arrival` | Lemma | `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.task_arrivals_size_at_non_arrival` | `task_arrivals_size_at_non_arrival_correspondence` | [view](3_printed_declarations/task_arrivals_size_at_non_arrival.md) |
| `task_arrivals_at_size_cases` | Lemma | `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.task_arrivals_at_size_cases` | `task_arrivals_at_size_cases_correspondence` | [view](3_printed_declarations/task_arrivals_at_size_cases.md) |
| `size_task_arrivals_between_eq0` | Lemma | `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.size_task_arrivals_between_eq0` | `size_task_arrivals_between_eq0_correspondence` | [view](3_printed_declarations/size_task_arrivals_between_eq0.md) |
| `jobs_exists_later` | Lemma | `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.jobs_exists_later` | `jobs_exists_later_correspondence` | [view](3_printed_declarations/jobs_exists_later.md) |
| `task_arrivals_at_size` | Lemma | `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.task_arrivals_at_size` | `task_arrivals_at_size_correspondence` | [view](3_printed_declarations/task_arrivals_at_size.md) |
| `size_task_arrivals_up_to_offset` | Lemma | `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.size_task_arrivals_up_to_offset` | `size_task_arrivals_up_to_offset_correspondence` | [view](3_printed_declarations/size_task_arrivals_up_to_offset.md) |
| `task_arrivals_up_to_size` | Lemma | `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.task_arrivals_up_to_size` | `task_arrivals_up_to_size_correspondence` | [view](3_printed_declarations/task_arrivals_up_to_size.md) |
| `eq_size_of_task_arrivals_seperated_by_period` | Lemma | `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.eq_size_of_task_arrivals_seperated_by_period` | `eq_size_of_task_arrivals_seperated_by_period_correspondence` | [view](3_printed_declarations/eq_size_of_task_arrivals_seperated_by_period.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPeriodicTaskArrivalsSizeCorrespondence`](4_correspondence/FactsPeriodicTaskArrivalsSizeCorrespondence.v) | Statement correspondences for `analysis/facts/periodic/task_arrivals_size.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
