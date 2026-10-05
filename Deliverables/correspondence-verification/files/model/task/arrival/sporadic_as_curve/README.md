# `model/task/arrival/sporadic_as_curve.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `MaxArrivalsSporadic` | Instance | `Prosa.Model.Task.Arrival.SporadicAsCurve.MaxArrivalsSporadic` | `MaxArrivalsSporadic_correspondence` | [view](3_printed_declarations/MaxArrivalsSporadic.md) |
| `sporadic_arrival_curve_valid` | Lemma | `Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_arrival_curve_valid` | `sporadic_arrival_curve_valid_correspondence` | [view](3_printed_declarations/sporadic_arrival_curve_valid.md) |
| `sporadic_task_sets_arrival_curve_valid` | Remark | `Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_task_sets_arrival_curve_valid` | `sporadic_task_sets_arrival_curve_valid_correspondence` | [view](3_printed_declarations/sporadic_task_sets_arrival_curve_valid.md) |
| `sporadic_arrival_curve_respects_max_arrivals` | Lemma | `Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_arrival_curve_respects_max_arrivals` | `sporadic_arrival_curve_respects_max_arrivals_correspondence` | [view](3_printed_declarations/sporadic_arrival_curve_respects_max_arrivals.md) |
| `sporadic_task_sets_respects_max_arrivals` | Remark | `Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_task_sets_respects_max_arrivals` | `sporadic_task_sets_respects_max_arrivals_correspondence` | [view](3_printed_declarations/sporadic_task_sets_respects_max_arrivals.md) |

## Certificates

| Module | Role |
|---|---|
| [`SporadicAsCurveCorrespondence`](4_correspondence/SporadicAsCurveCorrespondence.v) | Correspondences for `model/task/arrival/sporadic_as_curve.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
