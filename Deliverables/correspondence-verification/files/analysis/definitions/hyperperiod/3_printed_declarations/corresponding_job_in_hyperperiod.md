# `corresponding_job_in_hyperperiod`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.hyperperiod.corresponding_job_in_hyperperiod`
- Lean: `Prosa.Analysis.Definitions.Hyperperiod.corresponding_job_in_hyperperiod`
- Certificate: `corresponding_job_in_hyperperiod_correspondence`

## Official Rocq

```coq
corresponding_job_in_hyperperiod :
forall {Task : TaskType},
TaskOffset Task ->
PeriodicModel Task ->
forall {Job : JobType},
JobTask Job Task ->
JobArrival Job ->
TaskSet (Equality.sort Task) ->
arrival_sequence Job -> Equality.sort Job -> instant -> Equality.sort Task -> Equality.sort Job

corresponding_job_in_hyperperiod is not universe polymorphic
Arguments corresponding_job_in_hyperperiod {Task H H0 Job H1 H2} ts arr_seq j h tsk
corresponding_job_in_hyperperiod is transparent
Expands to: Constant prosa.analysis.definitions.hyperperiod.corresponding_job_in_hyperperiod
Declared in library prosa.analysis.definitions.hyperperiod, line 75, characters 13-45
@corresponding_job_in_hyperperiod
     : forall Task : TaskType,
       TaskOffset Task ->
       PeriodicModel Task ->
       forall Job : JobType,
       JobTask Job Task ->
       JobArrival Job ->
       TaskSet (Equality.sort Task) ->
       arrival_sequence Job -> Equality.sort Job -> instant -> Equality.sort Task -> Equality.sort Job
```

Body:

```coq
corresponding_job_in_hyperperiod =
fun (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType) 
  (H1 : JobTask Job Task) (H2 : JobArrival Job) (ts : TaskSet (Equality.sort Task))
  (arr_seq : arrival_sequence Job) =>
let O_max := @max_task_offset Task H ts in
let HP := @hyperperiod Task H0 ts in
fun (j : Equality.sort Job) (h : instant) (tsk : Equality.sort Task) =>
@nth (Equality.sort Job) j (@jobs_in_hyperperiod Task H0 Job H1 ts arr_seq h tsk)
  (@job_index_in_hyperperiod Task H0 Job H1 ts arr_seq j
     (@starting_instant_of_corresponding_hyperperiod Task H H0 Job H2 ts j) tsk)
     : forall {Task : TaskType},
       TaskOffset Task ->
       PeriodicModel Task ->
       forall {Job : JobType},
       JobTask Job Task ->
       JobArrival Job ->
       TaskSet (Equality.sort Task) ->
       arrival_sequence Job -> Equality.sort Job -> instant -> Equality.sort Task -> Equality.sort Job

Arguments corresponding_job_in_hyperperiod {Task H H0 Job H1 H2} ts arr_seq j h tsk
```

## Lean

```lean
@Prosa.Analysis.Definitions.Hyperperiod.corresponding_job_in_hyperperiod : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobArrival Job] →
                Prosa.Model.Task.Concept.TaskSet Task →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Job → Prosa.Behavior.Time.instant → Task → Job
```

Body:

```lean
def Prosa.Analysis.Definitions.Hyperperiod.corresponding_job_in_hyperperiod.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobArrival Job] →
                Prosa.Model.Task.Concept.TaskSet Task →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Job → Prosa.Behavior.Time.instant → Task → Job :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task]
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] ts arr_seq j h tsk =>
  (Prosa.Analysis.Definitions.Hyperperiod.jobs_in_hyperperiod ts arr_seq h tsk).getD
    (Prosa.Analysis.Definitions.Hyperperiod.job_index_in_hyperperiod ts arr_seq j
      (Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_corresponding_hyperperiod ts j) tsk)
    j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Hyperperiod_corresponding_job_in_hyperperiod
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       Job -> Prosa_Behavior_Time_instant -> Task -> Job
```

Body:

```coq
Prosa_Analysis_Definitions_Hyperperiod_corresponding_job_in_hyperperiod@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Offset_TaskOffset Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_13 : DecidableEq Job)
  (inst_16 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_13 Task
     inst_3)
  (inst_20 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_13)
  (ts : Prosa_Model_Task_Concept_TaskSet Task)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_13)
  (j : Job) (h : Prosa_Behavior_Time_instant) (tsk : Task) =>
List_getD Job
  (Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod Task
     inst_3
     inst_9 Job
     inst_13
     inst_16 ts arr_seq h tsk)
  (Prosa_Analysis_Definitions_Hyperperiod_job_index_in_hyperperiod Task
     inst_3
     inst_9 Job
     inst_13
     inst_16 ts arr_seq j
     (Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod Task
        inst_3
        inst_6
        inst_9 Job
        inst_13
        inst_20 ts j)
     tsk)
  j
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       Job -> Prosa_Behavior_Time_instant -> Task -> Job

Arguments Prosa_Analysis_Definitions_Hyperperiod_corresponding_job_in_hyperperiod 
  Task inst_3
  inst_6
  inst_9 Job
  inst_13
  inst_16
  inst_20 ts 
  arr_seq j h tsk
```
