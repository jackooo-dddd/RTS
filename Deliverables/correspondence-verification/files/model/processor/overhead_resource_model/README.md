# `model/processor/overhead_resource_model.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `time_spent_in_dispatch` | Definition | `Prosa.Model.Processor.OverheadResourceModel.time_spent_in_dispatch` | `time_spent_in_dispatch_correspondence` | [view](3_printed_declarations/time_spent_in_dispatch.md) |
| `time_spent_in_context_switch` | Definition | `Prosa.Model.Processor.OverheadResourceModel.time_spent_in_context_switch` | `time_spent_in_context_switch_correspondence` | [view](3_printed_declarations/time_spent_in_context_switch.md) |
| `time_spent_in_CRPD` | Definition | `Prosa.Model.Processor.OverheadResourceModel.time_spent_in_CRPD` | `time_spent_in_CRPD_correspondence` | [view](3_printed_declarations/time_spent_in_CRPD.md) |
| `time_spent_in_dispatch_is_bounded_by` | Definition | `Prosa.Model.Processor.OverheadResourceModel.time_spent_in_dispatch_is_bounded_by` | `time_spent_in_dispatch_is_bounded_by_correspondence` | [view](3_printed_declarations/time_spent_in_dispatch_is_bounded_by.md) |
| `time_spent_in_context_switch_is_bounded_by` | Definition | `Prosa.Model.Processor.OverheadResourceModel.time_spent_in_context_switch_is_bounded_by` | `time_spent_in_context_switch_is_bounded_by_correspondence` | [view](3_printed_declarations/time_spent_in_context_switch_is_bounded_by.md) |
| `time_spent_in_CRPD_is_bounded_by` | Definition | `Prosa.Model.Processor.OverheadResourceModel.time_spent_in_CRPD_is_bounded_by` | `time_spent_in_CRPD_is_bounded_by_correspondence` | [view](3_printed_declarations/time_spent_in_CRPD_is_bounded_by.md) |
| `dispatch_precedes_context_switch` | Definition | `Prosa.Model.Processor.OverheadResourceModel.dispatch_precedes_context_switch` | `dispatch_precedes_context_switch_correspondence` | [view](3_printed_declarations/dispatch_precedes_context_switch.md) |
| `context_switch_precedes_progress` | Definition | `Prosa.Model.Processor.OverheadResourceModel.context_switch_precedes_progress` | `context_switch_precedes_progress_correspondence` | [view](3_printed_declarations/context_switch_precedes_progress.md) |
| `context_switch_precedes_CRPD` | Definition | `Prosa.Model.Processor.OverheadResourceModel.context_switch_precedes_CRPD` | `context_switch_precedes_CRPD_correspondence` | [view](3_printed_declarations/context_switch_precedes_CRPD.md) |
| `overhead_resource_model` | Definition | `Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model` | `overhead_resource_model_correspondence` | [view](3_printed_declarations/overhead_resource_model.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
