# `model/processor/restricted_supply.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `processor_state` | Inductive | `Prosa.Model.Processor.RestrictedSupply.processor_state` | `rs_state_type_correspondence` | [view](3_printed_declarations/processor_state.md) |
| `rs_scheduled_on` | Definition | `Prosa.Model.Processor.RestrictedSupply.rs_scheduled_on` | `rs_scheduled_on_correspondence` | [view](3_printed_declarations/rs_scheduled_on.md) |
| `rs_supply_on` | Definition | `Prosa.Model.Processor.RestrictedSupply.rs_supply_on` | `rs_supply_on_correspondence` | [view](3_printed_declarations/rs_supply_on.md) |
| `rs_service_on` | Definition | `Prosa.Model.Processor.RestrictedSupply.rs_service_on` | `rs_service_on_correspondence` | [view](3_printed_declarations/rs_service_on.md) |
| `rs_processor_state` | Definition | `Prosa.Model.Processor.RestrictedSupply.rs_processor_state` | `rs_processor_state_correspondence` | [view](3_printed_declarations/rs_processor_state.md) |

## Certificates

| Module | Role |
|---|---|
| [`RestrictedSupplyBaseAdapter`](4_correspondence/RestrictedSupplyBaseAdapter.v) | Proves or defines `rs_false_elim`, `rs_false_to_strict`, `rs_coq_false_to_target` and 23 more. |
| [`RestrictedSupplyExactTypeGuards`](4_correspondence/RestrictedSupplyExactTypeGuards.v) | Exact-type checks refer directly to the compiled source and imported target declarations. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `RsTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
