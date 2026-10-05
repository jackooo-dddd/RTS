# `model/task/arrival/request_bound_functions.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `MaxRequestBound` | Class | `Prosa.Model.Task.Arrival.RequestBoundFunctions.MaxRequestBound` | `MaxRequestBound_source_total, MaxRequestBound_target_total` | [view](3_printed_declarations/MaxRequestBound.md) |
| `MinRequestBound` | Class | `Prosa.Model.Task.Arrival.RequestBoundFunctions.MinRequestBound` | `MinRequestBound_source_total, MinRequestBound_target_total` | [view](3_printed_declarations/MinRequestBound.md) |
| `valid_request_bound_function` | Definition | `Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_request_bound_function` | `valid_request_bound_function_correspondence` | [view](3_printed_declarations/valid_request_bound_function.md) |
| `respects_max_request_bound` | Definition | `Prosa.Model.Task.Arrival.RequestBoundFunctions.respects_max_request_bound` | `respects_max_request_bound_correspondence` | [view](3_printed_declarations/respects_max_request_bound.md) |
| `respects_min_request_bound` | Definition | `Prosa.Model.Task.Arrival.RequestBoundFunctions.respects_min_request_bound` | `respects_min_request_bound_correspondence` | [view](3_printed_declarations/respects_min_request_bound.md) |
| `valid_taskset_request_bound_function` | Definition | `Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_taskset_request_bound_function` | `valid_taskset_request_bound_function_correspondence` | [view](3_printed_declarations/valid_taskset_request_bound_function.md) |
| `taskset_respects_max_request_bound` | Definition | `Prosa.Model.Task.Arrival.RequestBoundFunctions.taskset_respects_max_request_bound` | `taskset_respects_max_request_bound_correspondence` | [view](3_printed_declarations/taskset_respects_max_request_bound.md) |
| `taskset_respects_min_request_bound` | Definition | `Prosa.Model.Task.Arrival.RequestBoundFunctions.taskset_respects_min_request_bound` | `taskset_respects_min_request_bound_correspondence` | [view](3_printed_declarations/taskset_respects_min_request_bound.md) |

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
