# `same_task`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.same_task`
- Lean: `Prosa.Model.Task.Concept.same_task`
- Certificate: ``

## Official Rocq

```coq
same_task :
forall {Job : JobType} {Task : TaskType}, JobTask Job Task -> Equality.sort Job -> Equality.sort Job -> bool

same_task is not universe polymorphic
Arguments same_task {Job Task H} j1 j2
same_task is transparent
Expands to: Constant prosa.model.task.concept.same_task
Declared in library prosa.model.task.concept, line 169, characters 13-22
@same_task
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task -> Equality.sort Job -> Equality.sort Job -> bool
```

Body:

```coq
same_task =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (j1 j2 : Equality.sort Job) =>
@job_task Job Task H j1 == @job_task Job Task H j2
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task -> Equality.sort Job -> Equality.sort Job -> bool

Arguments same_task {Job Task H} j1 j2
```

## Lean

```lean
@Prosa.Model.Task.Concept.same_task : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] → [Prosa.Model.Task.Concept.JobTask Job Task] → Job → Job → Bool
def Prosa.Model.Task.Concept.same_task.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] → [Prosa.Model.Task.Concept.JobTask Job Task] → Job → Job → Bool :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] j1 j2 =>
  decide (Prosa.Model.Task.Concept.job_task j1 = Prosa.Model.Task.Concept.job_task j2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_same_task
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Job -> Job -> Bool
```

Body:

```coq
Prosa_Model_Task_Concept_same_task@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0
Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask Job
                                                                      inst_3
                                                                      Task
                                                                      inst_7)
  (j1 j2 : Job) =>
Decidable_decide
  (@eq Task
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7
        inst_10 j1)
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7
        inst_10 j2))
  (inst_7
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7
        inst_10 j1)
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7
        inst_10 j2))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Job -> Job -> Bool

Arguments Prosa_Model_Task_Concept_same_task Job
  inst_3 Task
  inst_7
  inst_10 j1 j2
```
