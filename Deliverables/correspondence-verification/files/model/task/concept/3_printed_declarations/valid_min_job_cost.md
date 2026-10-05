# `valid_min_job_cost`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.concept.valid_min_job_cost`
- Lean: `Prosa.Model.Task.Concept.valid_min_job_cost`
- Certificate: ``

## Official Rocq

```coq
valid_min_job_cost :
forall {Task : TaskType},
TaskMinCost Task -> forall {Job : JobType}, JobTask Job Task -> JobCost Job -> Equality.sort Job -> bool

valid_min_job_cost is not universe polymorphic
Arguments valid_min_job_cost {Task H0 Job H2 H3} j
valid_min_job_cost is transparent
Expands to: Constant prosa.model.task.concept.valid_min_job_cost
Declared in library prosa.model.task.concept, line 102, characters 15-33
@valid_min_job_cost
     : forall Task : TaskType,
       TaskMinCost Task -> forall Job : JobType, JobTask Job Task -> JobCost Job -> Equality.sort Job -> bool
```

Body:

```coq
valid_min_job_cost =
fun (Task : TaskType) (H0 : TaskMinCost Task) (Job : JobType) (H2 : JobTask Job Task) 
  (H3 : JobCost Job) (j : Equality.sort Job) =>
@task_min_cost Task H0 (@job_task Job Task H2 j) <= @job_cost Job H3 j
     : forall {Task : TaskType},
       TaskMinCost Task ->
       forall {Job : JobType}, JobTask Job Task -> JobCost Job -> Equality.sort Job -> bool

Arguments valid_min_job_cost {Task H0 Job H2 H3} j
```

## Lean

```lean
@Prosa.Model.Task.Concept.valid_min_job_cost : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskMinCost Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Behavior.Job.JobCost Job] → Job → Bool
def Prosa.Model.Task.Concept.valid_min_job_cost.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskMinCost Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Behavior.Job.JobCost Job] → Job → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskMinCost Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobCost Job] j =>
  decide (Prosa.Model.Task.Concept.task_min_cost (Prosa.Model.Task.Concept.job_task j) ≤ Prosa.Behavior.Job.job_cost j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_valid_min_job_cost
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskMinCost Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_16
         Task inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_16 ->
       Job -> Bool
```

Body:

```coq
Prosa_Model_Task_Concept_valid_min_job_cost@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_9 : Prosa_Model_Task_Concept_TaskMinCost Task
                                                                     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_16 : DecidableEq Job)
  (inst_19 : Prosa_Model_Task_Concept_JobTask Job
                                                                      inst_16
                                                                      Task
                                                                      inst_3)
  (inst_23 : Prosa_Behavior_Job_JobCost Job
                                                                      inst_16)
  (j : Job) =>
Decidable_decide
  (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
     (Prosa_Model_Task_Concept_TaskMinCost_task_min_cost Task
        inst_3
        inst_9
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_16 Task
           inst_3
           inst_19 j))
     (Prosa_Behavior_Job_JobCost_job_cost Job inst_16
        inst_23 j))
  (Nat_decLe
     (Prosa_Model_Task_Concept_TaskMinCost_task_min_cost Task
        inst_3
        inst_9
        (Prosa_Model_Task_Concept_JobTask_job_task Job
           inst_16 Task
           inst_3
           inst_19 j))
     (Prosa_Behavior_Job_JobCost_job_cost Job inst_16
        inst_23 j))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskMinCost Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_16
         Task inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_16 ->
       Job -> Bool

Arguments Prosa_Model_Task_Concept_valid_min_job_cost Task
  inst_3
  inst_9 Job
  inst_16
  inst_19
  inst_23 tsk
```
