# `model/processor/overheads.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `proc_state` | Inductive | `Prosa.Model.Processor.Overheads.proc_state` | `ovh_state_target_roundtrip` | [view](3_printed_declarations/proc_state.md) |
| `overheads_scheduled_on` | Definition | `Prosa.Model.Processor.Overheads.overheads_scheduled_on` | `ovh_scheduled_on_correspondence` | [view](3_printed_declarations/overheads_scheduled_on.md) |
| `overheads_supply_on` | Definition | `Prosa.Model.Processor.Overheads.overheads_supply_on` | `ovh_supply_on_correspondence` | [view](3_printed_declarations/overheads_supply_on.md) |
| `overheads_service_on` | Definition | `Prosa.Model.Processor.Overheads.overheads_service_on` | `ovh_service_on_correspondence` | [view](3_printed_declarations/overheads_service_on.md) |
| `processor_state` | Definition | `Prosa.Model.Processor.Overheads.processor_state` | `ovh_processor_state_correspondence` | [view](3_printed_declarations/processor_state.md) |
| `scheduled_job` | Definition | `Prosa.Model.Processor.Overheads.scheduled_job` | `ovh_scheduled_job_correspondence` | [view](3_printed_declarations/scheduled_job.md) |
| `is_progress` | Definition | `Prosa.Model.Processor.Overheads.is_progress` | `ovh_is_progress_correspondence` | [view](3_printed_declarations/is_progress.md) |
| `is_context_switch` | Definition | `Prosa.Model.Processor.Overheads.is_context_switch` | `ovh_is_context_switch_correspondence` | [view](3_printed_declarations/is_context_switch.md) |
| `is_dispatch` | Definition | `Prosa.Model.Processor.Overheads.is_dispatch` | `ovh_is_dispatch_correspondence` | [view](3_printed_declarations/is_dispatch.md) |
| `is_CRPD` | Definition | `Prosa.Model.Processor.Overheads.is_CRPD` | `ovh_is_CRPD_correspondence` | [view](3_printed_declarations/is_CRPD.md) |
| `total_time_in_dispatch` | Definition | `Prosa.Model.Processor.Overheads.total_time_in_dispatch` | `ovh_total_time_in_dispatch_correspondence` | [view](3_printed_declarations/total_time_in_dispatch.md) |
| `total_time_in_context_switch` | Definition | `Prosa.Model.Processor.Overheads.total_time_in_context_switch` | `ovh_total_time_in_context_switch_correspondence` | [view](3_printed_declarations/total_time_in_context_switch.md) |
| `total_time_in_CRPD` | Definition | `Prosa.Model.Processor.Overheads.total_time_in_CRPD` | `ovh_total_time_in_CRPD_correspondence` | [view](3_printed_declarations/total_time_in_CRPD.md) |

## Certificates

| Module | Role |
|---|---|
| [`OverheadsExactTypeGuards`](4_correspondence/OverheadsExactTypeGuards.v) | These guards elaborate the official Rocq names and the actual imported compiled Lean names in the same Rocq environment as the certificates. |
| [`OverheadsCorrespondence`](4_correspondence/OverheadsCorrespondence.v) | Proves or defines `OvhSource`, `OvhTarget`, `ovh_option_to_imported` and 38 more. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `OvhTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
