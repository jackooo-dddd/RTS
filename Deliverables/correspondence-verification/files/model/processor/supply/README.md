# `model/processor/supply.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `supply_at` | Definition | `Prosa.Model.Processor.Supply.supply_at` | `` | [view](3_printed_declarations/supply_at.md) |
| `supply_during` | Definition | `Prosa.Model.Processor.Supply.supply_during` | `` | [view](3_printed_declarations/supply_during.md) |
| `has_supply` | Definition | `Prosa.Model.Processor.Supply.has_supply` | `` | [view](3_printed_declarations/has_supply.md) |
| `is_blackout` | Definition | `Prosa.Model.Processor.Supply.is_blackout` | `` | [view](3_printed_declarations/is_blackout.md) |
| `blackout_during` | Definition | `Prosa.Model.Processor.Supply.blackout_during` | `` | [view](3_printed_declarations/blackout_during.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
