# `job_index_in_hyperperiod`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.hyperperiod.job_index_in_hyperperiod`
- Lean: `Prosa.Analysis.Definitions.Hyperperiod.job_index_in_hyperperiod`
- Certificate: `job_index_in_hyperperiod_correspondence`

## Official Rocq

```coq
job_index_in_hyperperiod :
forall {Task : TaskType},
PeriodicModel Task ->
forall {Job : JobType},
JobTask Job Task ->
TaskSet (Equality.sort Task) ->
arrival_sequence Job -> Equality.sort Job -> instant -> Equality.sort Task -> nat

job_index_in_hyperperiod is not universe polymorphic
Arguments job_index_in_hyperperiod {Task H0 Job H1} ts arr_seq j h tsk
job_index_in_hyperperiod is transparent
Expands to: Constant prosa.analysis.definitions.hyperperiod.job_index_in_hyperperiod
Declared in library prosa.analysis.definitions.hyperperiod, line 69, characters 13-37
@job_index_in_hyperperiod
     : forall Task : TaskType,
       PeriodicModel Task ->
       forall Job : JobType,
       JobTask Job Task ->
       TaskSet (Equality.sort Task) ->
       arrival_sequence Job -> Equality.sort Job -> instant -> Equality.sort Task -> nat
```

Body:

```coq
job_index_in_hyperperiod =
fun (Task : TaskType) (H0 : PeriodicModel Task) (Job : JobType) (H1 : JobTask Job Task)
  (ts : TaskSet (Equality.sort Task)) (arr_seq : arrival_sequence Job) =>
let HP := @hyperperiod Task H0 ts in
fun (j : Equality.sort Job) (h : instant) (tsk : Equality.sort Task) =>
@index Job j (@jobs_in_hyperperiod Task H0 Job H1 ts arr_seq h tsk)
     : forall {Task : TaskType},
       PeriodicModel Task ->
       forall {Job : JobType},
       JobTask Job Task ->
       TaskSet (Equality.sort Task) ->
       arrival_sequence Job -> Equality.sort Job -> instant -> Equality.sort Task -> nat

Arguments job_index_in_hyperperiod {Task H0 Job H1} ts arr_seq j h tsk
```

## Lean

```lean
@Prosa.Analysis.Definitions.Hyperperiod.job_index_in_hyperperiod : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            Prosa.Model.Task.Concept.TaskSet Task →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → Prosa.Behavior.Time.instant → Task → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.Hyperperiod.job_index_in_hyperperiod.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            Prosa.Model.Task.Concept.TaskSet Task →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → Prosa.Behavior.Time.instant → Task → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] ts arr_seq j h tsk =>
  List.idxOf j (Prosa.Analysis.Definitions.Hyperperiod.jobs_in_hyperperiod ts arr_seq h tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Hyperperiod_job_index_in_hyperperiod
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       Job -> Prosa_Behavior_Time_instant -> Task -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_Hyperperiod_job_index_in_hyperperiod@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_13 : DecidableEq Job)
  (inst_16 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_13 Task
     inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_13)
  (j : Job) (h : Prosa_Behavior_Time_instant) (tsk : Task) =>
List_idxOf Job
  (instBEqOfDecidableEq Job inst_13) j
  (Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod Task
     inst_3
     inst_9 Job
     inst_13
     inst_16 ts arr_seq h tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       Job -> Prosa_Behavior_Time_instant -> Task -> Nat

Arguments Prosa_Analysis_Definitions_Hyperperiod_job_index_in_hyperperiod Task
  inst_3
  inst_9 Job
  inst_13
  inst_16 ts 
  arr_seq j h tsk
```
