# `analysis/facts/periodic/max_inter_arrival.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `max_inter_eq_period` | Instance | `Prosa.Analysis.Facts.Periodic.MaxInterArrival.max_inter_eq_period` | `max_inter_eq_period_correspondence` | [view](3_printed_declarations/max_inter_eq_period.md) |
| `valid_period_is_valid_max_inter_arrival_time` | Remark | `Prosa.Analysis.Facts.Periodic.MaxInterArrival.valid_period_is_valid_max_inter_arrival_time` | `valid_period_is_valid_max_inter_arrival_time_correspondence` | [view](3_printed_declarations/valid_period_is_valid_max_inter_arrival_time.md) |
| `periodic_model_respects_max_inter_arrival_model` | Remark | `Prosa.Analysis.Facts.Periodic.MaxInterArrival.periodic_model_respects_max_inter_arrival_model` | `periodic_model_respects_max_inter_arrival_model_correspondence` | [view](3_printed_declarations/periodic_model_respects_max_inter_arrival_model.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPeriodicMaxInterArrivalCorrespondence`](4_correspondence/FactsPeriodicMaxInterArrivalCorrespondence.v) | Correspondences for `analysis/facts/periodic/max_inter_arrival.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
