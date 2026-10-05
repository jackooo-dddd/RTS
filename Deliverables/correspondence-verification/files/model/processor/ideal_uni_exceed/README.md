# `model/processor/ideal_uni_exceed.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `exceedance_processor_state` | Inductive | `Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state` | `iue_target_roundtrip` | [view](3_printed_declarations/exceedance_processor_state.md) |
| `exceedance_processor_state_eqdef` | Definition | `Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state_eqdef` | `iue_eqdef_correspondence` | [view](3_printed_declarations/exceedance_processor_state_eqdef.md) |
| `eqn_exceedance_processor_state` | Lemma | `Prosa.Model.Processor.IdealUniExceed.eqn_exceedance_processor_state` | `iue_eqn_statement_correspondence` | [view](3_printed_declarations/eqn_exceedance_processor_state.md) |
| `exceedance_scheduled_on` | Definition | `Prosa.Model.Processor.IdealUniExceed.exceedance_scheduled_on` | `iue_scheduled_on_correspondence` | [view](3_printed_declarations/exceedance_scheduled_on.md) |
| `exceedance_supply_on` | Definition | `Prosa.Model.Processor.IdealUniExceed.exceedance_supply_on` | `iue_supply_on_correspondence` | [view](3_printed_declarations/exceedance_supply_on.md) |
| `exceedance_service_on` | Definition | `Prosa.Model.Processor.IdealUniExceed.exceedance_service_on` | `iue_service_on_correspondence` | [view](3_printed_declarations/exceedance_service_on.md) |
| `exceedance_proc_state` | Instance | `Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state` | `iue_processor_state_correspondence` | [view](3_printed_declarations/exceedance_proc_state.md) |

## Certificates

| Module | Role |
|---|---|
| [`IdealUniExceedExactTypeGuards`](4_correspondence/IdealUniExceedExactTypeGuards.v) | These checks elaborate the public source types and the actual imported compiled Lean declarations; neither side is a hand-written substitute. |
| [`IdealUniExceedCorrespondence`](4_correspondence/IdealUniExceedCorrespondence.v) | The source inductive and the imported Lean inductive remain distinct. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `IueTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
