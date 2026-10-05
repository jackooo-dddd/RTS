# `analysis/facts/periodic/arrival_separation.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `consecutive_job_separation` | Lemma | `Prosa.Analysis.Facts.Periodic.ArrivalSeparation.consecutive_job_separation` | `consecutive_job_separation_correspondence` | [view](3_printed_declarations/consecutive_job_separation.md) |
| `job_arrival_separation_when_index_diff_is_k` | Lemma | `Prosa.Analysis.Facts.Periodic.ArrivalSeparation.job_arrival_separation_when_index_diff_is_k` | `job_arrival_separation_when_index_diff_is_k_correspondence` | [view](3_printed_declarations/job_arrival_separation_when_index_diff_is_k.md) |
| `job_sep_periodic` | Lemma | `Prosa.Analysis.Facts.Periodic.ArrivalSeparation.job_sep_periodic` | `job_sep_periodic_correspondence` | [view](3_printed_declarations/job_sep_periodic.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPeriodicArrivalSeparationCorrespondence`](4_correspondence/FactsPeriodicArrivalSeparationCorrespondence.v) | Statement correspondences for `analysis/facts/periodic/arrival_separation.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
