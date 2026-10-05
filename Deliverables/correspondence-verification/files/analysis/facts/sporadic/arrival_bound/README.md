# `analysis/facts/sporadic/arrival_bound.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `max_sporadic_arrivals` | Definition | `Prosa.Analysis.Facts.Sporadic.ArrivalBound.max_sporadic_arrivals` | `max_sporadic_arrivals_correspondence` | [view](3_printed_declarations/max_sporadic_arrivals.md) |
| `arrival_of_nth_job` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalBound.arrival_of_nth_job` | `arrival_of_nth_job_correspondence` | [view](3_printed_declarations/arrival_of_nth_job.md) |
| `minimum_distance_for_n_sporadic_arrivals` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalBound.minimum_distance_for_n_sporadic_arrivals` | `minimum_distance_for_n_sporadic_arrivals_correspondence` | [view](3_printed_declarations/minimum_distance_for_n_sporadic_arrivals.md) |
| `sporadic_task_arrivals_bound` | Theorem | `Prosa.Analysis.Facts.Sporadic.ArrivalBound.sporadic_task_arrivals_bound` | `sporadic_task_arrivals_bound_correspondence` | [view](3_printed_declarations/sporadic_task_arrivals_bound.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsSporadicArrivalBoundCorrespondence`](4_correspondence/FactsSporadicArrivalBoundCorrespondence.v) | Correspondences for `analysis/facts/sporadic/arrival_bound.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
