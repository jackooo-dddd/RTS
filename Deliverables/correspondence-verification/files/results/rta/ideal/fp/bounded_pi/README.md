# `results/rta/ideal/fp/bounded_pi.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `is_in_search_space` | Definition | `Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space` | `is_in_search_space_correspondence` | [view](3_printed_declarations/is_in_search_space.md) |
| `instantiated_busy_intervals_are_bounded` | Lemma | `Prosa.Results.Rta.Ideal.Fp.BoundedPi.instantiated_busy_intervals_are_bounded` | `instantiated_busy_intervals_are_bounded_correspondence` | [view](3_printed_declarations/instantiated_busy_intervals_are_bounded.md) |
| `instantiated_task_interference_is_bounded` | Lemma | `Prosa.Results.Rta.Ideal.Fp.BoundedPi.instantiated_task_interference_is_bounded` | `instantiated_task_interference_is_bounded_correspondence` | [view](3_printed_declarations/instantiated_task_interference_is_bounded.md) |
| `A_is_in_concrete_search_space` | Lemma | `Prosa.Results.Rta.Ideal.Fp.BoundedPi.A_is_in_concrete_search_space` | `A_is_in_concrete_search_space_correspondence` | [view](3_printed_declarations/A_is_in_concrete_search_space.md) |
| `correct_search_space` | Corollary | `Prosa.Results.Rta.Ideal.Fp.BoundedPi.correct_search_space` | `correct_search_space_correspondence` | [view](3_printed_declarations/correct_search_space.md) |
| `uniprocessor_response_time_bound_fp` | Theorem | `Prosa.Results.Rta.Ideal.Fp.BoundedPi.uniprocessor_response_time_bound_fp` | `uniprocessor_response_time_bound_fp_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_fp.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtaIdealFpBoundedPiCorrespondence`](4_correspondence/RtaIdealFpBoundedPiCorrespondence.v) | Main certificate for results/rta/ideal/fp/bounded_pi.v: the helper part (no statement correspondences) of the accepted … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
