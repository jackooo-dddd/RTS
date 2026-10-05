# `analysis/abstract/ideal/cumulative_bounds.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `cumulative_priority_inversion_is_bounded` | Lemma | `Prosa.Analysis.Abstract.Ideal.CumulativeBounds.cumulative_priority_inversion_is_bounded` | `cumulative_priority_inversion_is_bounded_correspondence` | [view](3_printed_declarations/cumulative_priority_inversion_is_bounded.md) |
| `cumulative_interference_is_bounded_by_total_service` | Lemma | `Prosa.Analysis.Abstract.Ideal.CumulativeBounds.cumulative_interference_is_bounded_by_total_service` | `cumulative_interference_is_bounded_by_total_service_correspondence` | [view](3_printed_declarations/cumulative_interference_is_bounded_by_total_service.md) |

## Certificates

| Module | Role |
|---|---|
| [`IdealCumulativeBoundsCorrespondence`](4_correspondence/IdealCumulativeBoundsCorrespondence.v) | Main certificate for analysis/abstract/ideal/cumulative_bounds.v: the helper part (no statement correspondences) of the accepted … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
