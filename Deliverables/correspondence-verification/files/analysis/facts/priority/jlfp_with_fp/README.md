# `analysis/facts/priority/jlfp_with_fp.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `other_ep_task` | Definition | `Prosa.Analysis.Facts.Priority.JlfpWithFp.other_ep_task` | `other_ep_task_correspondence` | [view](3_printed_declarations/other_ep_task.md) |
| `hep_job_of_ep_other_task` | Definition | `Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_job_of_ep_other_task` | `hep_job_of_ep_other_task_correspondence` | [view](3_printed_declarations/hep_job_of_ep_other_task.md) |
| `hep_workload_from_other_ep_partitioned_by_tasks` | Lemma | `Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_workload_from_other_ep_partitioned_by_tasks` | `hep_workload_from_other_ep_partitioned_by_tasks_correspondence` | [view](3_printed_declarations/hep_workload_from_other_ep_partitioned_by_tasks.md) |
| `from_hp_task` | Definition | `Prosa.Analysis.Facts.Priority.JlfpWithFp.from_hp_task` | `from_hp_task_correspondence` | [view](3_printed_declarations/from_hp_task.md) |
| `hep_from_hp_task` | Definition | `Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_from_hp_task` | `hep_from_hp_task_correspondence` | [view](3_printed_declarations/hep_from_hp_task.md) |
| `hep_from_ep_task` | Definition | `Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_from_ep_task` | `hep_from_ep_task_correspondence` | [view](3_printed_declarations/hep_from_ep_task.md) |
| `hep_hp_workload_hp` | Lemma | `Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_hp_workload_hp` | `hep_hp_workload_hp_correspondence` | [view](3_printed_declarations/hep_hp_workload_hp.md) |
| `hep_workload_partitioning_taskwise` | Lemma | `Prosa.Analysis.Facts.Priority.JlfpWithFp.hep_workload_partitioning_taskwise` | `hep_workload_partitioning_taskwise_correspondence` | [view](3_printed_declarations/hep_workload_partitioning_taskwise.md) |

## Certificates

| Module | Role |
|---|---|
| [`JlfpWithFpCorrespondence`](4_correspondence/JlfpWithFpCorrespondence.v) | Certificates for `analysis/facts/priority/jlfp_with_fp.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
