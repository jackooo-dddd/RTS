# `valid_dynamic_suspensions`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.suspension.dynamic.valid_dynamic_suspensions`
- Lean: `Prosa.Model.Task.Suspension.Dynamic.valid_dynamic_suspensions`
- Certificate: `valid_dynamic_suspensions_correspondence`

## Official Rocq

```coq
valid_dynamic_suspensions :
forall {Job : JobType},
JobCost Job ->
JobSuspension Job -> forall {Task : TaskType}, JobTask Job Task -> TaskTotalSuspension Task -> Prop

valid_dynamic_suspensions is not universe polymorphic
Arguments valid_dynamic_suspensions {Job H H0 Task H1 H2}
valid_dynamic_suspensions is transparent
Expands to: Constant prosa.model.task.suspension.dynamic.valid_dynamic_suspensions
Declared in library prosa.model.task.suspension.dynamic, line 33, characters 13-38
@valid_dynamic_suspensions
     : forall Job : JobType,
       JobCost Job ->
       JobSuspension Job -> forall Task : TaskType, JobTask Job Task -> TaskTotalSuspension Task -> Prop
```

Body:

```coq
valid_dynamic_suspensions =
fun (Job : JobType) (H : JobCost Job) (H0 : JobSuspension Job) (Task : TaskType) 
  (H1 : JobTask Job Task) (H2 : TaskTotalSuspension Task) =>
forall j : Equality.sort Job,
is_true (@total_suspension Job H H0 j <= @task_total_suspension Task H2 (@job_task Job Task H1 j))
     : forall {Job : JobType},
       JobCost Job ->
       JobSuspension Job -> forall {Task : TaskType}, JobTask Job Task -> TaskTotalSuspension Task -> Prop

Arguments valid_dynamic_suspensions {Job H H0 Task H1 H2}
```

## Lean

```lean
@Prosa.Model.Task.Suspension.Dynamic.valid_dynamic_suspensions : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Readiness.Suspension.JobSuspension Job] →
        {Task : Prosa.Model.Task.Concept.TaskType} →
          [inst_3 : DecidableEq Task] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension Task] → Prop
```

Body:

```lean
def Prosa.Model.Task.Suspension.Dynamic.valid_dynamic_suspensions.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      [Prosa.Model.Readiness.Suspension.JobSuspension Job] →
        {Task : Prosa.Model.Task.Concept.TaskType} →
          [inst_3 : DecidableEq Task] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension Task] → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Readiness.Suspension.JobSuspension Job] {Task}
    [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Model.Task.Suspension.Dynamic.TaskTotalSuspension Task] =>
  ∀ (j : Job),
    Prosa.Model.Readiness.Suspension.total_suspension j ≤
      Prosa.Model.Task.Suspension.Dynamic.task_total_suspension (Prosa.Model.Task.Concept.job_task j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Suspension_Dynamic_valid_dynamic_suspensions
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Model_Readiness_Suspension_JobSuspension Job
         inst_3 ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_13 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_13 ->
       Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension Task
         inst_13 ->
       SProp
```

Body:

```coq
Prosa_Model_Task_Suspension_Dynamic_valid_dynamic_suspensions@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (inst_9 : Prosa_Model_Readiness_Suspension_JobSuspension
                                                                                Job
                                                                                inst_3)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_13 : DecidableEq Task)
  (inst_16 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_3
                                                                                Task
                                                                                inst_13)
  (inst_20 : Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension
                                                                                Task
                                                                                inst_13) =>
forall j : Job,
LE_le_inst1 Prosa_Behavior_Time_duration instLENat
  (Prosa_Model_Readiness_Suspension_total_suspension Job
     inst_3
     inst_6
     inst_9 j)
  (Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_task_total_suspension Task
     inst_13
     inst_20
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_13
        inst_16 j))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       Prosa_Model_Readiness_Suspension_JobSuspension Job
         inst_3 ->
       forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_13 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_13 ->
       Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension Task
         inst_13 ->
       SProp

Arguments Prosa_Model_Task_Suspension_Dynamic_valid_dynamic_suspensions Job
  inst_3
  inst_6
  inst_9 Task
  inst_13
  inst_16
  inst_20
```
