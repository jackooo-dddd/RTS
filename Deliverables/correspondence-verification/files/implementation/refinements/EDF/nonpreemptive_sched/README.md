# `implementation/refinements/EDF/nonpreemptive_sched.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `Task` | Definition | `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.Task` | `Task_source_total, Task_target_total` | [view](3_printed_declarations/Task.md) |
| `Job` | Definition | `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.Job` | `Job_source_total, Job_target_total` | [view](3_printed_declarations/Job.md) |
| `basic_ready_instance` | Instance | `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.basic_ready_instance` | `basic_ready_instance_correspondence` | [view](3_printed_declarations/basic_ready_instance.md) |
| `sched` | Definition | `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched` | `sched_correspondence` | [view](3_printed_declarations/sched.md) |
| `sched_jobs_must_be_ready_to_execute` | Lemma | `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_jobs_must_be_ready_to_execute` | `sched_jobs_must_be_ready_to_execute_correspondence` | [view](3_printed_declarations/sched_jobs_must_be_ready_to_execute.md) |
| `sched_valid` | Remark | `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_valid` | `sched_valid_correspondence` | [view](3_printed_declarations/sched_valid.md) |
| `sched_nonpreemptive_next` | Lemma | `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_nonpreemptive_next` | `sched_nonpreemptive_next_correspondence` | [view](3_printed_declarations/sched_nonpreemptive_next.md) |
| `sched_nonpreemptive` | Lemma | `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_nonpreemptive` | `sched_nonpreemptive_correspondence` | [view](3_printed_declarations/sched_nonpreemptive.md) |
| `respects_policy_at_preemption_point_edf_np` | Lemma | `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.respects_policy_at_preemption_point_edf_np` | `respects_policy_at_preemption_point_edf_np_correspondence` | [view](3_printed_declarations/respects_policy_at_preemption_point_edf_np.md) |

## Certificates

| Module | Role |
|---|---|
| [`RefEDFNPSchedCorrespondence`](4_correspondence/RefEDFNPSchedCorrespondence.v) | Correspondences for `implementation/refinements/EDF/nonpreemptive_sched.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
