# `analysis/facts/workload/edf_athep_bound.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `total_workload_shorten_range` | Lemma | `Prosa.Analysis.Facts.Workload.EdfAthepBound.total_workload_shorten_range` | `total_workload_shorten_range_correspondence` | [view](3_printed_declarations/total_workload_shorten_range.md) |
| `sum_of_workloads_is_at_most_bound_on_total_hep_workload` | Corollary | `Prosa.Analysis.Facts.Workload.EdfAthepBound.sum_of_workloads_is_at_most_bound_on_total_hep_workload` | `sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence` | [view](3_printed_declarations/sum_of_workloads_is_at_most_bound_on_total_hep_workload.md) |
| `bound_on_athep_workload_is_valid` | Corollary | `Prosa.Analysis.Facts.Workload.EdfAthepBound.bound_on_athep_workload_is_valid` | `bound_on_athep_workload_is_valid_correspondence` | [view](3_printed_declarations/bound_on_athep_workload_is_valid.md) |
| `bound_on_athep_workload_monotone` | Lemma | `Prosa.Analysis.Facts.Workload.EdfAthepBound.bound_on_athep_workload_monotone` | `bound_on_athep_workload_monotone_correspondence` | [view](3_printed_declarations/bound_on_athep_workload_monotone.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsEdfAthepBoundCorrespondence`](4_correspondence/FactsEdfAthepBoundCorrespondence.v) | Statement correspondences for `analysis/facts/workload/edf_athep_bound.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
