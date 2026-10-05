# `implementation/refinements/EDF/preemptive_sched.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `Task` | Definition | `Prosa.Implementation.Refinements.EDF.PreemptiveSched.Task` | `Task_source_total, Task_target_total` | [view](3_printed_declarations/Task.md) |
| `Job` | Definition | `Prosa.Implementation.Refinements.EDF.PreemptiveSched.Job` | `Job_source_total, Job_target_total` | [view](3_printed_declarations/Job.md) |
| `basic_ready_instance` | Instance | `Prosa.Implementation.Refinements.EDF.PreemptiveSched.basic_ready_instance` | `basic_ready_instance_correspondence` | [view](3_printed_declarations/basic_ready_instance.md) |
| `sched` | Definition | `Prosa.Implementation.Refinements.EDF.PreemptiveSched.sched` | `sched_correspondence` | [view](3_printed_declarations/sched.md) |
| `sched_valid` | Remark | `Prosa.Implementation.Refinements.EDF.PreemptiveSched.sched_valid` | `sched_valid_correspondence` | [view](3_printed_declarations/sched_valid.md) |
| `respects_policy_at_preemption_point_edf_fp` | Lemma | `Prosa.Implementation.Refinements.EDF.PreemptiveSched.respects_policy_at_preemption_point_edf_fp` | `respects_policy_at_preemption_point_edf_fp_correspondence` | [view](3_printed_declarations/respects_policy_at_preemption_point_edf_fp.md) |

## Certificates

| Module | Role |
|---|---|
| [`RefEDFPSchedCorrespondence`](4_correspondence/RefEDFPSchedCorrespondence.v) | Correspondences for `implementation/refinements/EDF/preemptive_sched.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
