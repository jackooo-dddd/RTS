# `analysis/facts/periodic/arrival_times.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `periodic_arrival_times` | Lemma | `Prosa.Analysis.Facts.Periodic.ArrivalTimes.periodic_arrival_times` | `periodic_arrival_times_correspondence` | [view](3_printed_declarations/periodic_arrival_times.md) |
| `job_arrival_times` | Lemma | `Prosa.Analysis.Facts.Periodic.ArrivalTimes.job_arrival_times` | `job_arrival_times_correspondence` | [view](3_printed_declarations/job_arrival_times.md) |
| `job_arr_index` | Lemma | `Prosa.Analysis.Facts.Periodic.ArrivalTimes.job_arr_index` | `job_arr_index_correspondence` | [view](3_printed_declarations/job_arr_index.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPeriodicArrivalTimesCorrespondence`](4_correspondence/FactsPeriodicArrivalTimesCorrespondence.v) | Statement correspondences for `analysis/facts/periodic/arrival_times.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
