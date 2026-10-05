# `analysis/abstract/lower_bound_on_service.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `interference_is_complement_to_schedule` | Lemma | `Prosa.Analysis.Abstract.LowerBoundOnService.interference_is_complement_to_schedule` | `interference_is_complement_to_schedule_correspondence` | [view](3_printed_declarations/interference_is_complement_to_schedule.md) |
| `service_and_interference_bounded` | Remark | `Prosa.Analysis.Abstract.LowerBoundOnService.service_and_interference_bounded` | `service_and_interference_bounded_correspondence` | [view](3_printed_declarations/service_and_interference_bounded.md) |
| `j_receives_enough_service` | Theorem | `Prosa.Analysis.Abstract.LowerBoundOnService.j_receives_enough_service` | `j_receives_enough_service_correspondence` | [view](3_printed_declarations/j_receives_enough_service.md) |

## Certificates

| Module | Role |
|---|---|
| [`LowerBoundOnServiceCorrespondence`](4_correspondence/LowerBoundOnServiceCorrespondence.v) | Statement correspondences for `analysis/abstract/lower_bound_on_service.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
