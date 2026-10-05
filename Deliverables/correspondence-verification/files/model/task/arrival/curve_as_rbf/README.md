# `model/task/arrival/curve_as_rbf.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_max_rbf` | Definition | `Prosa.Model.Task.Arrival.CurveAsRbf.task_max_rbf` | `task_max_rbf_correspondence` | [view](3_printed_declarations/task_max_rbf.md) |
| `task_min_rbf` | Definition | `Prosa.Model.Task.Arrival.CurveAsRbf.task_min_rbf` | `task_min_rbf_correspondence` | [view](3_printed_declarations/task_min_rbf.md) |
| `MaxArrivalsRBF` | Instance | `Prosa.Model.Task.Arrival.CurveAsRbf.MaxArrivalsRBF` | `MaxArrivalsRBF_correspondence` | [view](3_printed_declarations/MaxArrivalsRBF.md) |
| `MinArrivalsRBF` | Instance | `Prosa.Model.Task.Arrival.CurveAsRbf.MinArrivalsRBF` | `MinArrivalsRBF_correspondence` | [view](3_printed_declarations/MinArrivalsRBF.md) |
| `valid_arrival_curve_to_max_rbf` | Theorem | `Prosa.Model.Task.Arrival.CurveAsRbf.valid_arrival_curve_to_max_rbf` | `valid_arrival_curve_to_max_rbf_correspondence` | [view](3_printed_declarations/valid_arrival_curve_to_max_rbf.md) |
| `valid_arrival_curve_to_min_rbf` | Theorem | `Prosa.Model.Task.Arrival.CurveAsRbf.valid_arrival_curve_to_min_rbf` | `valid_arrival_curve_to_min_rbf_correspondence` | [view](3_printed_declarations/valid_arrival_curve_to_min_rbf.md) |
| `respects_arrival_curve_to_max_rbf` | Theorem | `Prosa.Model.Task.Arrival.CurveAsRbf.respects_arrival_curve_to_max_rbf` | `respects_arrival_curve_to_max_rbf_correspondence` | [view](3_printed_declarations/respects_arrival_curve_to_max_rbf.md) |
| `respects_arrival_curve_to_min_rbf` | Theorem | `Prosa.Model.Task.Arrival.CurveAsRbf.respects_arrival_curve_to_min_rbf` | `respects_arrival_curve_to_min_rbf_correspondence` | [view](3_printed_declarations/respects_arrival_curve_to_min_rbf.md) |
| `valid_taskset_arrival_curve_to_max_rbf` | Corollary | `Prosa.Model.Task.Arrival.CurveAsRbf.valid_taskset_arrival_curve_to_max_rbf` | `valid_taskset_arrival_curve_to_max_rbf_correspondence` | [view](3_printed_declarations/valid_taskset_arrival_curve_to_max_rbf.md) |
| `valid_taskset_arrival_curve_to_min_rbf` | Corollary | `Prosa.Model.Task.Arrival.CurveAsRbf.valid_taskset_arrival_curve_to_min_rbf` | `valid_taskset_arrival_curve_to_min_rbf_correspondence` | [view](3_printed_declarations/valid_taskset_arrival_curve_to_min_rbf.md) |
| `taskset_respects_arrival_curve_to_max_rbf` | Corollary | `Prosa.Model.Task.Arrival.CurveAsRbf.taskset_respects_arrival_curve_to_max_rbf` | `taskset_respects_arrival_curve_to_max_rbf_correspondence` | [view](3_printed_declarations/taskset_respects_arrival_curve_to_max_rbf.md) |
| `taskset_respects_arrival_curve_to_min_rbf` | Corollary | `Prosa.Model.Task.Arrival.CurveAsRbf.taskset_respects_arrival_curve_to_min_rbf` | `taskset_respects_arrival_curve_to_min_rbf_correspondence` | [view](3_printed_declarations/taskset_respects_arrival_curve_to_min_rbf.md) |

## Certificates

| Module | Role |
|---|---|
| [`CurveAsRbfCorrespondence`](4_correspondence/CurveAsRbfCorrespondence.v) | Certificates for `model/task/arrival/curve_as_rbf.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
