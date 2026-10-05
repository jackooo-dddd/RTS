# `results/rta/ideal/fp/nonseq/bounded_pi.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `instantiated_busy_intervals_are_bounded` | Lemma | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.instantiated_busy_intervals_are_bounded` | `instantiated_busy_intervals_are_bounded_correspondence` | [view](3_printed_declarations/instantiated_busy_intervals_are_bounded.md) |
| `IBF` | Definition | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.IBF` | `IBF_correspondence` | [view](3_printed_declarations/IBF.md) |
| `self_intf_bound_case1` | Lemma | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.self_intf_bound_case1` | `self_intf_bound_case1_correspondence` | [view](3_printed_declarations/self_intf_bound_case1.md) |
| `self_intf_bound_case2` | Lemma | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.self_intf_bound_case2` | `self_intf_bound_case2_correspondence` | [view](3_printed_declarations/self_intf_bound_case2.md) |
| `self_intf_bound` | Lemma | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.self_intf_bound` | `self_intf_bound_correspondence` | [view](3_printed_declarations/self_intf_bound.md) |
| `instantiated_task_interference_is_bounded` | Lemma | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.instantiated_task_interference_is_bounded` | `instantiated_task_interference_is_bounded_correspondence` | [view](3_printed_declarations/instantiated_task_interference_is_bounded.md) |
| `is_in_concrete_search_space` | Definition | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.is_in_concrete_search_space` | `is_in_concrete_search_space_correspondence` | [view](3_printed_declarations/is_in_concrete_search_space.md) |
| `A_is_in_concrete_search_space` | Lemma | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.A_is_in_concrete_search_space` | `A_is_in_concrete_search_space_correspondence` | [view](3_printed_declarations/A_is_in_concrete_search_space.md) |
| `correct_search_space` | Corollary | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.correct_search_space` | `correct_search_space_correspondence` | [view](3_printed_declarations/correct_search_space.md) |
| `uniprocessor_response_time_bound_fp` | Theorem | `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.uniprocessor_response_time_bound_fp` | `uniprocessor_response_time_bound_fp_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_fp.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtaIdealFpNonseqBoundedPiCorrespondence`](4_correspondence/RtaIdealFpNonseqBoundedPiCorrespondence.v) | Main certificate for results/rta/ideal/fp/nonseq/bounded_pi.v: the helper part (no statement correspondences) of the accepted … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
