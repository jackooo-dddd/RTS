# `results/rta/arm/edf/fully_nonpreemptive.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `busy_window_recurrence_solution` | Definition | `Prosa.Results.Rta.Arm.Edf.FullyNonpreemptive.busy_window_recurrence_solution` | `busy_window_recurrence_solution_correspondence` | [view](3_printed_declarations/busy_window_recurrence_solution.md) |
| `rta_recurrence_solution` | Definition | `Prosa.Results.Rta.Arm.Edf.FullyNonpreemptive.rta_recurrence_solution` | `rta_recurrence_solution_correspondence` | [view](3_printed_declarations/rta_recurrence_solution.md) |
| `uniprocessor_response_time_bound_fully_nonpreemptive_edf` | Theorem | `Prosa.Results.Rta.Arm.Edf.FullyNonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf` | `uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_fully_nonpreemptive_edf.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtaArmEdfFullyNonpreemptiveCorrespondence`](4_correspondence/RtaArmEdfFullyNonpreemptiveCorrespondence.v) | Correspondences for `results/rta/arm/edf/fully_nonpreemptive.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
