# `analysis/facts/model/ideal/service_of_jobs.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `low_service_implies_existence_of_idle_time_rs` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.ServiceOfJobs.low_service_implies_existence_of_idle_time_rs` | `low_service_implies_existence_of_idle_time_rs_correspondence` | [view](3_printed_declarations/low_service_implies_existence_of_idle_time_rs.md) |
| `low_service_implies_existence_of_idle_time` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.ServiceOfJobs.low_service_implies_existence_of_idle_time` | `low_service_implies_existence_of_idle_time_correspondence` | [view](3_printed_declarations/low_service_implies_existence_of_idle_time.md) |

## Certificates

| Module | Role |
|---|---|
| [`IdealServiceOfJobsCorrespondence`](4_correspondence/IdealServiceOfJobsCorrespondence.v) | Statement correspondences for `analysis/facts/model/ideal/service_of_jobs.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
