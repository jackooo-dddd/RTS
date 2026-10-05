# `behavior/ready.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `JobReady` | Class | `Prosa.Behavior.Ready.JobReady` | `` | [view](3_printed_declarations/JobReady.md) |
| `backlogged` | Definition | `Prosa.Behavior.Ready.backlogged` | `` | [view](3_printed_declarations/backlogged.md) |
| `jobs_come_from_arrival_sequence` | Definition | `Prosa.Behavior.Ready.jobs_come_from_arrival_sequence` | `` | [view](3_printed_declarations/jobs_come_from_arrival_sequence.md) |
| `jobs_must_arrive_to_execute` | Definition | `Prosa.Behavior.Ready.jobs_must_arrive_to_execute` | `` | [view](3_printed_declarations/jobs_must_arrive_to_execute.md) |
| `jobs_must_be_ready_to_execute` | Definition | `Prosa.Behavior.Ready.jobs_must_be_ready_to_execute` | `` | [view](3_printed_declarations/jobs_must_be_ready_to_execute.md) |
| `completed_jobs_dont_execute` | Definition | `Prosa.Behavior.Ready.completed_jobs_dont_execute` | `` | [view](3_printed_declarations/completed_jobs_dont_execute.md) |
| `valid_schedule` | Definition | `Prosa.Behavior.Ready.valid_schedule` | `` | [view](3_printed_declarations/valid_schedule.md) |

## Certificates

| Module | Role |
|---|---|
| [`ReadyArrivalCorrespondence`](4_correspondence/ReadyArrivalCorrespondence.v) | Fourteen compositional certificates for the official v0.6 definitions and the actual imported production Lean bodies. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
