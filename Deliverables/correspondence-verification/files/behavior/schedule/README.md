# `behavior/schedule.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `ProcessorState` | Class | `Prosa.Behavior.Schedule.ProcessorState` | `` | [view](3_printed_declarations/ProcessorState.md) |
| `scheduled_in` | Definition | `Prosa.Behavior.Schedule.ProcessorState.scheduled_in` | `` | [view](3_printed_declarations/scheduled_in.md) |
| `supply_in` | Definition | `Prosa.Behavior.Schedule.ProcessorState.supply_in` | `` | [view](3_printed_declarations/supply_in.md) |
| `service_in` | Definition | `Prosa.Behavior.Schedule.ProcessorState.service_in` | `` | [view](3_printed_declarations/service_in.md) |
| `schedule` | Definition | `Prosa.Behavior.Schedule.schedule` | `` | [view](3_printed_declarations/schedule.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SchSourceTrue`, `SchTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
