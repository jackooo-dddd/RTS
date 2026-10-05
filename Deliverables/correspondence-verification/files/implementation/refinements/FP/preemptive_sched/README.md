# `implementation/refinements/FP/preemptive_sched.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `Task` | Definition | `Prosa.Implementation.Refinements.FP.PreemptiveSched.Task` | `Task_source_total, Task_target_total` | [view](3_printed_declarations/Task.md) |
| `Job` | Definition | `Prosa.Implementation.Refinements.FP.PreemptiveSched.Job` | `Job_source_total, Job_target_total` | [view](3_printed_declarations/Job.md) |
| `sequential_ready_instance` | Instance | `Prosa.Implementation.Refinements.FP.PreemptiveSched.sequential_ready_instance` | `sequential_ready_instance_correspondence` | [view](3_printed_declarations/sequential_ready_instance.md) |
| `sched` | Definition | `Prosa.Implementation.Refinements.FP.PreemptiveSched.sched` | `sched_correspondence` | [view](3_printed_declarations/sched.md) |
| `sched_valid` | Remark | `Prosa.Implementation.Refinements.FP.PreemptiveSched.sched_valid` | `sched_valid_correspondence` | [view](3_printed_declarations/sched_valid.md) |
| `respects_policy_at_preemption_point` | Lemma | `Prosa.Implementation.Refinements.FP.PreemptiveSched.respects_policy_at_preemption_point` | `respects_policy_at_preemption_point_correspondence` | [view](3_printed_declarations/respects_policy_at_preemption_point.md) |

## Certificates

| Module | Role |
|---|---|
| [`RefFPPSchedCorrespondence`](4_correspondence/RefFPPSchedCorrespondence.v) | Correspondences for `implementation/refinements/FP/preemptive_sched.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
