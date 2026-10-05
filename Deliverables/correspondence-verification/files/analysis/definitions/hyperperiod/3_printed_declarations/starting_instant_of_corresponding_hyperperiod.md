# `starting_instant_of_corresponding_hyperperiod`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.hyperperiod.starting_instant_of_corresponding_hyperperiod`
- Lean: `Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_corresponding_hyperperiod`
- Certificate: `starting_instant_of_corresponding_hyperperiod_correspondence`

## Official Rocq

```coq
starting_instant_of_corresponding_hyperperiod :
forall {Task : TaskType},
TaskOffset Task ->
PeriodicModel Task ->
forall {Job : JobType}, JobArrival Job -> TaskSet (Equality.sort Task) -> Equality.sort Job -> nat

starting_instant_of_corresponding_hyperperiod is not universe polymorphic
Arguments starting_instant_of_corresponding_hyperperiod {Task H H0 Job H2} ts j
starting_instant_of_corresponding_hyperperiod is transparent
Expands to: Constant prosa.analysis.definitions.hyperperiod.starting_instant_of_corresponding_hyperperiod
Declared in library prosa.analysis.definitions.hyperperiod, line 60, characters 13-58
@starting_instant_of_corresponding_hyperperiod
     : forall Task : TaskType,
       TaskOffset Task ->
       PeriodicModel Task ->
       forall Job : JobType, JobArrival Job -> TaskSet (Equality.sort Task) -> Equality.sort Job -> nat
```

Body:

```coq
starting_instant_of_corresponding_hyperperiod =
fun (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType) 
  (H2 : JobArrival Job) (ts : TaskSet (Equality.sort Task)) =>
let O_max := @max_task_offset Task H ts in
let HP := @hyperperiod Task H0 ts in
fun j : Equality.sort Job => @starting_instant_of_hyperperiod Task H H0 ts (@job_arrival Job H2 j)
     : forall {Task : TaskType},
       TaskOffset Task ->
       PeriodicModel Task ->
       forall {Job : JobType}, JobArrival Job -> TaskSet (Equality.sort Task) -> Equality.sort Job -> nat

Arguments starting_instant_of_corresponding_hyperperiod {Task H H0 Job H2} ts j
```

## Lean

```lean
@Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_corresponding_hyperperiod : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst : DecidableEq Job] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Model.Task.Concept.TaskSet Task → Job → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_corresponding_hyperperiod.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst : DecidableEq Job] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Model.Task.Concept.TaskSet Task → Job → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task]
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    ts j =>
  Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_hyperperiod ts (Prosa.Behavior.Job.job_arrival j)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Job -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod@{u_1 u_2 Lean.u_1+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Offset_TaskOffset
                                                                                Task
                                                                                inst_3)
  (inst_9 : Prosa_Model_Task_Arrival_Periodic_PeriodicModel
                                                                                Task
                                                                                inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_13 : DecidableEq Job)
  (inst_20 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_13)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) (j : Job) =>
Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_hyperperiod Task
  inst_3
  inst_6
  inst_9 ts
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_13
     inst_20 j)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       Prosa_Model_Task_Concept_TaskSet Task -> Job -> Nat

Arguments Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod 
  Task inst_3
  inst_6
  inst_9 Job
  inst_13
  inst_20 ts 
  j
```
