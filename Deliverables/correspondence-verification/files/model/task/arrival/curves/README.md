# `model/task/arrival/curves.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `MaxArrivals` | Class | `Prosa.Model.Task.Arrival.Curves.MaxArrivals` | `MaxArrivals_source_total, MaxArrivals_target_total` | [view](3_printed_declarations/MaxArrivals.md) |
| `MinArrivals` | Class | `Prosa.Model.Task.Arrival.Curves.MinArrivals` | `MinArrivals_source_total, MinArrivals_target_total` | [view](3_printed_declarations/MinArrivals.md) |
| `MinSeparation` | Class | `Prosa.Model.Task.Arrival.Curves.MinSeparation` | `MinSeparation_source_total, MinSeparation_target_total` | [view](3_printed_declarations/MinSeparation.md) |
| `MaxSeparation` | Class | `Prosa.Model.Task.Arrival.Curves.MaxSeparation` | `MaxSeparation_source_total, MaxSeparation_target_total` | [view](3_printed_declarations/MaxSeparation.md) |
| `valid_arrival_curve` | Definition | `Prosa.Model.Task.Arrival.Curves.valid_arrival_curve` | `valid_arrival_curve_correspondence` | [view](3_printed_declarations/valid_arrival_curve.md) |
| `respects_max_arrivals` | Definition | `Prosa.Model.Task.Arrival.Curves.respects_max_arrivals` | `respects_max_arrivals_correspondence` | [view](3_printed_declarations/respects_max_arrivals.md) |
| `respects_min_arrivals` | Definition | `Prosa.Model.Task.Arrival.Curves.respects_min_arrivals` | `respects_min_arrivals_correspondence` | [view](3_printed_declarations/respects_min_arrivals.md) |
| `respects_min_separation` | Definition | `Prosa.Model.Task.Arrival.Curves.respects_min_separation` | `respects_min_separation_correspondence` | [view](3_printed_declarations/respects_min_separation.md) |
| `respects_max_separation` | Definition | `Prosa.Model.Task.Arrival.Curves.respects_max_separation` | `respects_max_separation_correspondence` | [view](3_printed_declarations/respects_max_separation.md) |
| `valid_taskset_arrival_curve` | Definition | `Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve` | `valid_taskset_arrival_curve_correspondence` | [view](3_printed_declarations/valid_taskset_arrival_curve.md) |
| `taskset_respects_max_arrivals` | Definition | `Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals` | `taskset_respects_max_arrivals_correspondence` | [view](3_printed_declarations/taskset_respects_max_arrivals.md) |
| `taskset_respects_min_arrivals` | Definition | `Prosa.Model.Task.Arrival.Curves.taskset_respects_min_arrivals` | `taskset_respects_min_arrivals_correspondence` | [view](3_printed_declarations/taskset_respects_min_arrivals.md) |
| `taskset_respects_max_separation` | Definition | `Prosa.Model.Task.Arrival.Curves.taskset_respects_max_separation` | `taskset_respects_max_separation_correspondence` | [view](3_printed_declarations/taskset_respects_max_separation.md) |
| `taskset_respects_min_separation` | Definition | `Prosa.Model.Task.Arrival.Curves.taskset_respects_min_separation` | `taskset_respects_min_separation_correspondence` | [view](3_printed_declarations/taskset_respects_min_separation.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
