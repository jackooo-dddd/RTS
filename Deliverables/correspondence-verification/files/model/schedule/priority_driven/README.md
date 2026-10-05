# `model/schedule/priority_driven.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `respects_JLDP_policy_at_preemption_point` | Definition | `Prosa.Model.Schedule.PriorityDriven.respects_JLDP_policy_at_preemption_point` | `respects_JLDP_policy_at_preemption_point_correspondence` | [view](3_printed_declarations/respects_JLDP_policy_at_preemption_point.md) |
| `respects_JLFP_policy_at_preemption_point` | Definition | `Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point` | `respects_JLFP_policy_at_preemption_point_correspondence` | [view](3_printed_declarations/respects_JLFP_policy_at_preemption_point.md) |
| `respects_FP_policy_at_preemption_point` | Definition | `Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point` | `respects_FP_policy_at_preemption_point_correspondence` | [view](3_printed_declarations/respects_FP_policy_at_preemption_point.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
