# `model/processor/multiprocessor.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `processor` | Definition | `Prosa.Model.Processor.Multiprocessor.processor` | `processor_source_total, processor_target_total` | [view](3_printed_declarations/processor.md) |
| `multiprocessor_state` | Definition | `Prosa.Model.Processor.Multiprocessor.multiprocessor_state` | `multiprocessor_state_source_total, multiprocessor_state_target_total` | [view](3_printed_declarations/multiprocessor_state.md) |
| `multiproc_scheduled_on` | Definition | `Prosa.Model.Processor.Multiprocessor.multiproc_scheduled_on` | `multiproc_scheduled_on_correspondence` | [view](3_printed_declarations/multiproc_scheduled_on.md) |
| `multiproc_supply_on` | Definition | `Prosa.Model.Processor.Multiprocessor.multiproc_supply_on` | `multiproc_supply_on_correspondence` | [view](3_printed_declarations/multiproc_supply_on.md) |
| `multiproc_service_on` | Definition | `Prosa.Model.Processor.Multiprocessor.multiproc_service_on` | `multiproc_service_on_correspondence` | [view](3_printed_declarations/multiproc_service_on.md) |
| `multiproc_service_in_eq` | Lemma | `Prosa.Model.Processor.Multiprocessor.multiproc_service_in_eq` | `multiproc_service_in_eq_correspondence` | [view](3_printed_declarations/multiproc_service_in_eq.md) |

## Certificates

| Module | Role |
|---|---|
| [`MultiprocessorCorrespondence`](4_correspondence/MultiprocessorCorrespondence.v) | Correspondences for `model/processor/multiprocessor.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
