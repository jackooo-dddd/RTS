# `analysis/facts/shifted_job_costs.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_costs_shifted` | Definition | `Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_shifted` | `job_costs_shifted_correspondence` | [view](3_printed_declarations/job_costs_shifted.md) |
| `job_costs_in_oi` | Instance | `Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_in_oi` | `job_costs_in_oi_correspondence` | [view](3_printed_declarations/job_costs_in_oi.md) |
| `job_costs_shifted_valid` | Lemma | `Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_shifted_valid` | `job_costs_shifted_valid_correspondence` | [view](3_printed_declarations/job_costs_shifted_valid.md) |

## Certificates

| Module | Role |
|---|---|
| [`ShiftedJobCostsCorrespondence`](4_correspondence/ShiftedJobCostsCorrespondence.v) | Correspondences for `analysis/facts/shifted_job_costs.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
