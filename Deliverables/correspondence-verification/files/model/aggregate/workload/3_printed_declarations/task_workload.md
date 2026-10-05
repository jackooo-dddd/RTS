# `task_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.workload.task_workload`
- Lean: `Prosa.Model.Aggregate.Workload.task_workload`
- Certificate: `task_workload_correspondence`

## Official Rocq

```coq
task_workload :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> JobCost Job -> Equality.sort Task -> seq (Equality.sort Job) -> nat

task_workload is not universe polymorphic
Arguments task_workload {Task Job H0 H1} tsk jobs%seq_scope
task_workload is transparent
Expands to: Constant prosa.model.aggregate.workload.task_workload
Declared in library prosa.model.aggregate.workload, line 24, characters 13-26
@task_workload
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> JobCost Job -> Equality.sort Task -> seq (Equality.sort Job) -> nat
```

Body:

```coq
task_workload =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobCost Job) (tsk : Equality.sort Task) =>
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> JobCost Job -> Equality.sort Task -> seq (Equality.sort Job) -> nat

Arguments task_workload {Task Job H0 H1} tsk jobs%seq_scope
```

## Lean

```lean
@Prosa.Model.Aggregate.Workload.task_workload : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Behavior.Job.JobCost Job] → Task → List Job → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.Workload.task_workload.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Behavior.Job.JobCost Job] → Task → List Job → ℕ :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobCost Job] tsk jobs =>
  Prosa.Model.Aggregate.Workload.workload_of_jobs (Prosa.Model.Task.Concept.job_of_task tsk) jobs
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_Workload_task_workload
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_7 ->
       Task -> List Job -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_Workload_task_workload@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                            Job
                                                                            inst_7
                                                                            Task
                                                                            inst_3)
  (inst_14 : Prosa_Behavior_Job_JobCost Job
                                                                            inst_7)
  (tsk : Task) (jobs : List Job) =>
Prosa_Model_Aggregate_Workload_workload_of_jobs Job
  inst_7
  inst_14
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_7 Task
     inst_3
     inst_10 tsk)
  jobs
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_7 ->
       Task -> List Job -> Nat

Arguments Prosa_Model_Aggregate_Workload_task_workload Task
  inst_3 Job
  inst_7
  inst_10
  inst_14 tsk jobs
```
