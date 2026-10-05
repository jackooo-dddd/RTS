# `job_of_task`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.job_of_task`
- Lean: `Prosa.Model.Task.Concept.job_of_task`
- Certificate: ``

## Official Rocq

```coq
job_of_task :
forall {Job : JobType} {Task : TaskType}, JobTask Job Task -> Equality.sort Task -> Equality.sort Job -> bool

job_of_task is not universe polymorphic
Arguments job_of_task {Job Task H} tsk j
job_of_task is transparent
Expands to: Constant prosa.model.task.concept.job_of_task
Declared in library prosa.model.task.concept, line 179, characters 13-24
@job_of_task
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task -> Equality.sort Task -> Equality.sort Job -> bool
```

Body:

```coq
job_of_task =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (tsk : Equality.sort Task)
  (j : Equality.sort Job) =>
@job_task Job Task H j == tsk
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task -> Equality.sort Task -> Equality.sort Job -> bool

Arguments job_of_task {Job Task H} tsk j
```

## Lean

```lean
@Prosa.Model.Task.Concept.job_of_task : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] → [Prosa.Model.Task.Concept.JobTask Job Task] → Task → Job → Bool
def Prosa.Model.Task.Concept.job_of_task.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] → [Prosa.Model.Task.Concept.JobTask Job Task] → Task → Job → Bool :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] tsk j =>
  decide (Prosa.Model.Task.Concept.job_task j = tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_job_of_task
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Task -> Job -> Bool
```

Body:

```coq
Prosa_Model_Task_Concept_job_of_task@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0
Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask Job
                                                                      inst_3
                                                                      Task
                                                                      inst_7)
  (tsk : Task) (j : Job) =>
Decidable_decide
  (@eq Task
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7
        inst_10 j)
     tsk)
  (inst_7
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7
        inst_10 j)
     tsk)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Task -> Job -> Bool

Arguments Prosa_Model_Task_Concept_job_of_task Job
  inst_3 Task
  inst_7
  inst_10 tsk j2
```
