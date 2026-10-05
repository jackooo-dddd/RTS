# `model/task/concept.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `TaskType` | Definition | `Prosa.Model.Task.Concept.TaskType` | `` | [view](3_printed_declarations/TaskType.md) |
| `JobTask` | Class | `Prosa.Model.Task.Concept.JobTask` | `` | [view](3_printed_declarations/JobTask.md) |
| `TaskDeadline` | Class | `Prosa.Model.Task.Concept.TaskDeadline` | `` | [view](3_printed_declarations/TaskDeadline.md) |
| `TaskCost` | Class | `Prosa.Model.Task.Concept.TaskCost` | `` | [view](3_printed_declarations/TaskCost.md) |
| `TaskMinCost` | Class | `Prosa.Model.Task.Concept.TaskMinCost` | `` | [view](3_printed_declarations/TaskMinCost.md) |
| `task_cost_positive` | Definition | `Prosa.Model.Task.Concept.task_cost_positive` | `` | [view](3_printed_declarations/task_cost_positive.md) |
| `task_cost_at_most_deadline` | Definition | `Prosa.Model.Task.Concept.task_cost_at_most_deadline` | `` | [view](3_printed_declarations/task_cost_at_most_deadline.md) |
| `valid_job_cost` | Definition | `Prosa.Model.Task.Concept.valid_job_cost` | `` | [view](3_printed_declarations/valid_job_cost.md) |
| `jobs_have_valid_job_costs` | Definition | `Prosa.Model.Task.Concept.jobs_have_valid_job_costs` | `` | [view](3_printed_declarations/jobs_have_valid_job_costs.md) |
| `arrivals_have_valid_job_costs` | Definition | `Prosa.Model.Task.Concept.arrivals_have_valid_job_costs` | `` | [view](3_printed_declarations/arrivals_have_valid_job_costs.md) |
| `valid_min_job_cost` | Definition | `Prosa.Model.Task.Concept.valid_min_job_cost` | `` | [view](3_printed_declarations/valid_min_job_cost.md) |
| `jobs_have_valid_min_job_costs` | Definition | `Prosa.Model.Task.Concept.jobs_have_valid_min_job_costs` | `` | [view](3_printed_declarations/jobs_have_valid_min_job_costs.md) |
| `arrivals_have_valid_min_job_costs` | Definition | `Prosa.Model.Task.Concept.arrivals_have_valid_min_job_costs` | `` | [view](3_printed_declarations/arrivals_have_valid_min_job_costs.md) |
| `TaskSet` | Definition | `Prosa.Model.Task.Concept.TaskSet` | `` | [view](3_printed_declarations/TaskSet.md) |
| `all_jobs_from_taskset` | Definition | `Prosa.Model.Task.Concept.all_jobs_from_taskset` | `` | [view](3_printed_declarations/all_jobs_from_taskset.md) |
| `same_task` | Definition | `Prosa.Model.Task.Concept.same_task` | `` | [view](3_printed_declarations/same_task.md) |
| `same_task_sym` | Remark | `Prosa.Model.Task.Concept.same_task_sym` | `` | [view](3_printed_declarations/same_task_sym.md) |
| `job_of_task` | Definition | `Prosa.Model.Task.Concept.job_of_task` | `` | [view](3_printed_declarations/job_of_task.md) |
| `diff_task` | Remark | `Prosa.Model.Task.Concept.diff_task` | `` | [view](3_printed_declarations/diff_task.md) |

## Certificates

| Module | Role |
|---|---|
| [`ConceptOperations`](4_correspondence/ConceptOperations.v) | Target-local, small operation slice. |
| [`ConceptClasses`](4_correspondence/ConceptClasses.v) | Observable class interfaces for the actual imported one-field Lean records. |
| [`ReadyArrivalCorrespondence`](4_correspondence/ReadyArrivalCorrespondence.v) | Fourteen compositional certificates for the official v0.6 definitions and the actual imported production Lean bodies. |
| [`ConceptCorrespondence`](4_correspondence/ConceptCorrespondence.v) | All v0.6 Concept value definitions and two theorem types are related to their exact imported Lean bodies. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
