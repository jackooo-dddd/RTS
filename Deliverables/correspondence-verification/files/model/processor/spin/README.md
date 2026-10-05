# `model/processor/spin.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `processor_state` | Inductive | `Prosa.Model.Processor.Spin.processor_state` | `spin_state_type_correspondence` | [view](3_printed_declarations/processor_state.md) |
| `spin_scheduled_on` | Definition | `Prosa.Model.Processor.Spin.spin_scheduled_on` | `spin_scheduled_on_correspondence` | [view](3_printed_declarations/spin_scheduled_on.md) |
| `spin_supply_on` | Definition | `Prosa.Model.Processor.Spin.spin_supply_on` | `spin_supply_on_correspondence` | [view](3_printed_declarations/spin_supply_on.md) |
| `spin_service_on` | Definition | `Prosa.Model.Processor.Spin.spin_service_on` | `spin_service_on_correspondence` | [view](3_printed_declarations/spin_service_on.md) |
| `pstate_instance` | Definition | `Prosa.Model.Processor.Spin.pstate_instance` | `pstate_instance_correspondence` | [view](3_printed_declarations/pstate_instance.md) |

## Certificates

| Module | Role |
|---|---|
| [`SpinBaseAdapter`](4_correspondence/SpinBaseAdapter.v) | Artifact-local proof adapter for the actual imported Spin module. |
| [`SpinExactTypeGuards`](4_correspondence/SpinExactTypeGuards.v) | These checks bind the certificate to the compiled official source and imported Lean artifact. |
| [`SpinCorrespondence`](4_correspondence/SpinCorrespondence.v) | Proves or defines `SpinSource`, `SpinTarget`, `spin_to_target` and 24 more. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SpinTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
