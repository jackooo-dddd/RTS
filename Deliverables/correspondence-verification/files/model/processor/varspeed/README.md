# `model/processor/varspeed.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `processor_state` | Inductive | `Prosa.Model.Processor.Varspeed.processor_state` | `vs_state_type_correspondence` | [view](3_printed_declarations/processor_state.md) |
| `varspeed_scheduled_on` | Definition | `Prosa.Model.Processor.Varspeed.varspeed_scheduled_on` | `vs_scheduled_on_correspondence` | [view](3_printed_declarations/varspeed_scheduled_on.md) |
| `varspeed_supply_on` | Definition | `Prosa.Model.Processor.Varspeed.varspeed_supply_on` | `vs_supply_on_correspondence` | [view](3_printed_declarations/varspeed_supply_on.md) |
| `varspeed_service_on` | Definition | `Prosa.Model.Processor.Varspeed.varspeed_service_on` | `vs_service_on_correspondence` | [view](3_printed_declarations/varspeed_service_on.md) |
| `pstate_instance` | Definition | `Prosa.Model.Processor.Varspeed.pstate_instance` | `vs_processor_state_correspondence` | [view](3_printed_declarations/pstate_instance.md) |

## Certificates

| Module | Role |
|---|---|
| [`VarspeedBaseAdapter`](4_correspondence/VarspeedBaseAdapter.v) | Artifact-local adapters for the actual ImportedVarspeedFull datatype identities. |
| [`VarspeedExactTypeGuards`](4_correspondence/VarspeedExactTypeGuards.v) | These checks refer to the compiled patched official source and to the actual imported Lean artifact. |
| [`VarspeedCorrespondence`](4_correspondence/VarspeedCorrespondence.v) | Proves or defines `VsSource`, `VsTarget`, `vs_to_target` and 20 more. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `VsTrue`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
