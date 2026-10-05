# `model/processor/platform_properties.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `unit_service_proc_model` | Definition | `Prosa.Model.Processor.PlatformProperties.unit_service_proc_model` | `unit_service_proc_model_correspondence` | [view](3_printed_declarations/unit_service_proc_model.md) |
| `ideal_progress_proc_model` | Definition | `Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model` | `ideal_progress_proc_model_correspondence` | [view](3_printed_declarations/ideal_progress_proc_model.md) |
| `uniprocessor_model` | Definition | `Prosa.Model.Processor.PlatformProperties.uniprocessor_model` | `uniprocessor_model_correspondence` | [view](3_printed_declarations/uniprocessor_model.md) |
| `unit_supply_proc_model` | Definition | `Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model` | `unit_supply_proc_model_correspondence` | [view](3_printed_declarations/unit_supply_proc_model.md) |
| `unit_supply_is_unit_service` | Remark | `Prosa.Model.Processor.PlatformProperties.unit_supply_is_unit_service` | `unit_supply_is_unit_service_statement_correspondence` | [view](3_printed_declarations/unit_supply_is_unit_service.md) |
| `fully_consuming_proc_model` | Definition | `Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model` | `fully_consuming_proc_model_correspondence` | [view](3_printed_declarations/fully_consuming_proc_model.md) |

## Certificates

| Module | Role |
|---|---|
| [`PlatformPropertiesExactTypeGuards`](4_correspondence/PlatformPropertiesExactTypeGuards.v) | These guards are separate from the correspondence proof. |
| [`PlatformPropertiesCorrespondence`](4_correspondence/PlatformPropertiesCorrespondence.v) | The processor-state relation is the previously certified, two-sided observational representation relation, recompiled against this exact imported artifact. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SchSourceTrue`, `SchTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
