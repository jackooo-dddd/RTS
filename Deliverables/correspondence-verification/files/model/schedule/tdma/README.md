# `model/schedule/tdma.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `TDMA_slot` | Definition | `Prosa.Model.Schedule.Tdma.TDMA_slot` | `TDMA_slot_source_total, TDMA_slot_target_total` | [view](3_printed_declarations/TDMA_slot.md) |
| `TDMA_slot_order` | Definition | `Prosa.Model.Schedule.Tdma.TDMA_slot_order` | `TDMA_slot_order_source_total, TDMA_slot_order_target_total` | [view](3_printed_declarations/TDMA_slot_order.md) |
| `TDMAPolicy` | Class | `Prosa.Model.Schedule.Tdma.TDMAPolicy` | `tdma_policy_source_total, tdma_policy_target_total` | [view](3_printed_declarations/TDMAPolicy.md) |
| `transitive_slot_order` | Definition | `Prosa.Model.Schedule.Tdma.transitive_slot_order` | `transitive_slot_order_correspondence` | [view](3_printed_declarations/transitive_slot_order.md) |
| `total_slot_order` | Definition | `Prosa.Model.Schedule.Tdma.total_slot_order` | `total_slot_order_correspondence` | [view](3_printed_declarations/total_slot_order.md) |
| `antisymmetric_slot_order` | Definition | `Prosa.Model.Schedule.Tdma.antisymmetric_slot_order` | `antisymmetric_slot_order_correspondence` | [view](3_printed_declarations/antisymmetric_slot_order.md) |
| `valid_time_slot` | Definition | `Prosa.Model.Schedule.Tdma.valid_time_slot` | `valid_time_slot_correspondence` | [view](3_printed_declarations/valid_time_slot.md) |
| `valid_TDMAPolicy` | Definition | `Prosa.Model.Schedule.Tdma.valid_TDMAPolicy` | `valid_TDMAPolicy_correspondence` | [view](3_printed_declarations/valid_TDMAPolicy.md) |
| `TDMA_cycle` | Definition | `Prosa.Model.Schedule.Tdma.TDMA_cycle` | `TDMA_cycle_correspondence` | [view](3_printed_declarations/TDMA_cycle.md) |
| `task_slot_offset` | Definition | `Prosa.Model.Schedule.Tdma.task_slot_offset` | `task_slot_offset_correspondence` | [view](3_printed_declarations/task_slot_offset.md) |
| `task_in_time_slot` | Definition | `Prosa.Model.Schedule.Tdma.task_in_time_slot` | `task_in_time_slot_correspondence` | [view](3_printed_declarations/task_in_time_slot.md) |
| `job_in_time_slot` | Definition | `Prosa.Model.Schedule.Tdma.job_in_time_slot` | `job_in_time_slot_correspondence` | [view](3_printed_declarations/job_in_time_slot.md) |
| `sched_implies_in_slot` | Definition | `Prosa.Model.Schedule.Tdma.sched_implies_in_slot` | `sched_implies_in_slot_correspondence` | [view](3_printed_declarations/sched_implies_in_slot.md) |
| `backlogged_implies_not_in_slot_or_other_job_sched` | Definition | `Prosa.Model.Schedule.Tdma.backlogged_implies_not_in_slot_or_other_job_sched` | `backlogged_implies_not_in_slot_or_other_job_sched_correspondence` | [view](3_printed_declarations/backlogged_implies_not_in_slot_or_other_job_sched.md) |
| `respects_TDMA_policy` | Definition | `Prosa.Model.Schedule.Tdma.respects_TDMA_policy` | `respects_TDMA_policy_correspondence` | [view](3_printed_declarations/respects_TDMA_policy.md) |

## Certificates

| Module | Role |
|---|---|
| [`TdmaJobTaskAdapter`](4_correspondence/TdmaJobTaskAdapter.v) | Equality-preserving relation for the accepted JobTask dependency. |
| [`TdmaProcessorOperations`](4_correspondence/TdmaProcessorOperations.v) | Only the already certified finite scheduled-in truth interface and the state/core observations actually consumed by Scheduled are used below. |
| [`TdmaArrivalOperations`](4_correspondence/TdmaArrivalOperations.v) | Pointwise relation for the already accepted ArrivalSequence dependency. |
| [`TdmaScheduleCorrespondence`](4_correspondence/TdmaScheduleCorrespondence.v) | Input relation: the arrival sequences are pointwise related. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `EdfSourceTrue`, `HEq`, `HEq_inst1`, `SeqsetTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
