# `results/rta/ideal/fp/bounded_nps.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `priority_inversion_is_bounded_by_blocking` | Lemma | `Prosa.Results.Rta.Ideal.Fp.BoundedNps.priority_inversion_is_bounded_by_blocking` | `priority_inversion_is_bounded_by_blocking_correspondence` | [view](3_printed_declarations/priority_inversion_is_bounded_by_blocking.md) |
| `priority_inversion_is_bounded` | Lemma | `Prosa.Results.Rta.Ideal.Fp.BoundedNps.priority_inversion_is_bounded` | `priority_inversion_is_bounded_correspondence` | [view](3_printed_declarations/priority_inversion_is_bounded.md) |
| `uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments` | Theorem | `Prosa.Results.Rta.Ideal.Fp.BoundedNps.uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments` | `uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments.md) |

## Certificates

| Module | Role |
|---|---|
| [`RtaIdealFpBoundedNpsCorrespondence`](4_correspondence/RtaIdealFpBoundedNpsCorrespondence.v) | Main certificate for results/rta/ideal/fp/bounded_nps.v: the helper part (no statement correspondences) of the accepted … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
