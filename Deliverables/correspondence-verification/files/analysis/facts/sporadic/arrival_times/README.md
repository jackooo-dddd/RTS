# `analysis/facts/sporadic/arrival_times.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `lower_index_implies_earlier_arrival` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalTimes.lower_index_implies_earlier_arrival` | `lower_index_implies_earlier_arrival_correspondence` | [view](3_printed_declarations/lower_index_implies_earlier_arrival.md) |
| `same_jobs_iff_same_arr` | Lemma | `Prosa.Analysis.Facts.Sporadic.ArrivalTimes.same_jobs_iff_same_arr` | `same_jobs_iff_same_arr_correspondence` | [view](3_printed_declarations/same_jobs_iff_same_arr.md) |
| `uneq_job_uneq_arr` | Corollary | `Prosa.Analysis.Facts.Sporadic.ArrivalTimes.uneq_job_uneq_arr` | `uneq_job_uneq_arr_correspondence` | [view](3_printed_declarations/uneq_job_uneq_arr.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsSporadicArrivalTimesCorrespondence`](4_correspondence/FactsSporadicArrivalTimesCorrespondence.v) | Correspondences for `analysis/facts/sporadic/arrival_times.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
