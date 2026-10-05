# `results/rta/rs/fp/fully_nonpreemptive.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `busy_window_recurrence_solution` | Definition | `Prosa.Results.Rta.Rs.Fp.FullyNonpreemptive.busy_window_recurrence_solution` | `busy_window_recurrence_solution_correspondence` | [view](3_printed_declarations/busy_window_recurrence_solution.md) |
| `rta_recurrence_solution` | Definition | `Prosa.Results.Rta.Rs.Fp.FullyNonpreemptive.rta_recurrence_solution` | `rta_recurrence_solution_correspondence` | [view](3_printed_declarations/rta_recurrence_solution.md) |
| `uniprocessor_response_time_bound_fully_nonpreemptive_fp` | Theorem | `Prosa.Results.Rta.Rs.Fp.FullyNonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp` | `uniprocessor_response_time_bound_fully_nonpreemptive_fp_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_fully_nonpreemptive_fp.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtaRsFpFullyNonpreemptiveCorrespondence`](4_correspondence/RtaRsFpFullyNonpreemptiveCorrespondence.v) | Correspondences for `results/rta/rs/fp/fully_nonpreemptive.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `PdTrue`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
