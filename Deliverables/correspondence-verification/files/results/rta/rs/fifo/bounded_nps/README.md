# `results/rta/rs/fifo/bounded_nps.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `busy_window_recurrence_solution` | Definition | `Prosa.Results.Rta.Rs.Fifo.BoundedNps.busy_window_recurrence_solution` | `busy_window_recurrence_solution_correspondence` | [view](3_printed_declarations/busy_window_recurrence_solution.md) |
| `rta_recurrence_solution` | Definition | `Prosa.Results.Rta.Rs.Fifo.BoundedNps.rta_recurrence_solution` | `rta_recurrence_solution_correspondence` | [view](3_printed_declarations/rta_recurrence_solution.md) |
| `uniprocessor_response_time_bound_fifo` | Theorem | `Prosa.Results.Rta.Rs.Fifo.BoundedNps.uniprocessor_response_time_bound_fifo` | `uniprocessor_response_time_bound_fifo_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_fifo.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtaRsFifoBoundedNpsCorrespondence`](4_correspondence/RtaRsFifoBoundedNpsCorrespondence.v) | Correspondences for `results/rta/rs/fifo/bounded_nps.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
