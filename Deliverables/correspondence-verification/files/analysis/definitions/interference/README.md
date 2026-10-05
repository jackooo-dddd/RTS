# `analysis/definitions/interference.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `hp_task_interference` | Definition | `Prosa.Analysis.Definitions.Interference.hp_task_interference` | `hp_task_interference_correspondence` | [view](3_printed_declarations/hp_task_interference.md) |
| `ep_task_hep_job` | Definition | `Prosa.Analysis.Definitions.Interference.ep_task_hep_job` | `ep_task_hep_job_correspondence` | [view](3_printed_declarations/ep_task_hep_job.md) |
| `other_ep_task_hep_job` | Definition | `Prosa.Analysis.Definitions.Interference.other_ep_task_hep_job` | `other_ep_task_hep_job_correspondence` | [view](3_printed_declarations/other_ep_task_hep_job.md) |
| `hep_job_from_other_ep_task_interference` | Definition | `Prosa.Analysis.Definitions.Interference.hep_job_from_other_ep_task_interference` | `hep_job_from_other_ep_task_interference_correspondence` | [view](3_printed_declarations/hep_job_from_other_ep_task_interference.md) |
| `hp_task_hep_job` | Definition | `Prosa.Analysis.Definitions.Interference.hp_task_hep_job` | `hp_task_hep_job_correspondence` | [view](3_printed_declarations/hp_task_hep_job.md) |
| `hep_job_from_hp_task_interference` | Definition | `Prosa.Analysis.Definitions.Interference.hep_job_from_hp_task_interference` | `hep_job_from_hp_task_interference_correspondence` | [view](3_printed_declarations/hep_job_from_hp_task_interference.md) |
| `cumulative_interference_from_hep_jobs_from_hp_tasks` | Definition | `Prosa.Analysis.Definitions.Interference.cumulative_interference_from_hep_jobs_from_hp_tasks` | `cumulative_interference_from_hep_jobs_from_hp_tasks_correspondence` | [view](3_printed_declarations/cumulative_interference_from_hep_jobs_from_hp_tasks.md) |
| `cumulative_interference_from_hep_jobs_from_other_ep_tasks` | Definition | `Prosa.Analysis.Definitions.Interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks` | `cumulative_interference_from_hep_jobs_from_other_ep_tasks_correspondence` | [view](3_printed_declarations/cumulative_interference_from_hep_jobs_from_other_ep_tasks.md) |
| `another_hep_job_interference` | Definition | `Prosa.Analysis.Definitions.Interference.another_hep_job_interference` | `another_hep_job_interference_correspondence` | [view](3_printed_declarations/another_hep_job_interference.md) |
| `another_task_hep_job_interference` | Definition | `Prosa.Analysis.Definitions.Interference.another_task_hep_job_interference` | `another_task_hep_job_interference_correspondence` | [view](3_printed_declarations/another_task_hep_job_interference.md) |
| `another_hep_job_of_same_task_interference` | Definition | `Prosa.Analysis.Definitions.Interference.another_hep_job_of_same_task_interference` | `another_hep_job_of_same_task_interference_correspondence` | [view](3_printed_declarations/another_hep_job_of_same_task_interference.md) |
| `other_hep_jobs_interfering_workload` | Definition | `Prosa.Analysis.Definitions.Interference.other_hep_jobs_interfering_workload` | `other_hep_jobs_interfering_workload_correspondence` | [view](3_printed_declarations/other_hep_jobs_interfering_workload.md) |
| `cumulative_another_hep_job_interference` | Definition | `Prosa.Analysis.Definitions.Interference.cumulative_another_hep_job_interference` | `cumulative_another_hep_job_interference_correspondence` | [view](3_printed_declarations/cumulative_another_hep_job_interference.md) |
| `cumulative_another_task_hep_job_interference` | Definition | `Prosa.Analysis.Definitions.Interference.cumulative_another_task_hep_job_interference` | `cumulative_another_task_hep_job_interference_correspondence` | [view](3_printed_declarations/cumulative_another_task_hep_job_interference.md) |
| `cumulative_other_hep_jobs_interfering_workload` | Definition | `Prosa.Analysis.Definitions.Interference.cumulative_other_hep_jobs_interfering_workload` | `cumulative_other_hep_jobs_interfering_workload_correspondence` | [view](3_printed_declarations/cumulative_other_hep_jobs_interfering_workload.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
