# `valid_task_max_inter_arrival_time`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.task_max_inter_arrival.valid_task_max_inter_arrival_time`
- Lean: `Prosa.Model.Task.Arrival.Task_max_inter_arrival.valid_task_max_inter_arrival_time`
- Certificate: `valid_task_max_inter_arrival_time_correspondence`

## Official Rocq

```coq
valid_task_max_inter_arrival_time :
forall {Task : TaskType},
TaskMaxInterArrival Task ->
forall {Job : JobType},
JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

valid_task_max_inter_arrival_time is not universe polymorphic
Arguments valid_task_max_inter_arrival_time {Task H Job H0 H1} arr_seq tsk
valid_task_max_inter_arrival_time is transparent
Expands to: Constant prosa.model.task.arrival.task_max_inter_arrival.valid_task_max_inter_arrival_time
Declared in library prosa.model.task.arrival.task_max_inter_arrival, line 50, characters 13-46
@valid_task_max_inter_arrival_time
     : forall Task : TaskType,
       TaskMaxInterArrival Task ->
       forall Job : JobType,
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop
```

Body:

```coq
valid_task_max_inter_arrival_time =
fun (Task : TaskType) (H : TaskMaxInterArrival Task) (Job : JobType) (H0 : JobTask Job Task)
  (H1 : JobArrival Job) (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) =>
is_true (@positive_task_max_inter_arrival_time Task H tsk) /\
@arr_sep_task_max_inter_arrival Task H Job H0 H1 arr_seq tsk
     : forall {Task : TaskType},
       TaskMaxInterArrival Task ->
       forall {Job : JobType},
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

Arguments valid_task_max_inter_arrival_time {Task H Job H0 H1} arr_seq tsk
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Task_max_inter_arrival.valid_task_max_inter_arrival_time : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop
def Prosa.Model.Task.Arrival.Task_max_inter_arrival.valid_task_max_inter_arrival_time.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Task_max_inter_arrival.TaskMaxInterArrival Task] {Job}
    [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] arr_seq tsk =>
  Prosa.Model.Task.Arrival.Task_max_inter_arrival.positive_task_max_inter_arrival_time tsk = true ∧
    Prosa.Model.Task.Arrival.Task_max_inter_arrival.arr_sep_task_max_inter_arrival arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Task_max_inter_arrival_valid_task_max_inter_arrival_time
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Task_max_inter_arrival_valid_task_max_inter_arrival_time@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_10 Task
     inst_3)
  (inst_17 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (tsk : Task) =>
And
  (@eq Bool
     (Prosa_Model_Task_Arrival_Task_max_inter_arrival_positive_task_max_inter_arrival_time Task
        inst_3
        inst_6 tsk)
     Bool_true)
  (Prosa_Model_Task_Arrival_Task_max_inter_arrival_arr_sep_task_max_inter_arrival Task
     inst_3
     inst_6 Job
     inst_10
     inst_13
     inst_17 arr_seq tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Task_max_inter_arrival_TaskMaxInterArrival Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Task -> SProp

Arguments Prosa_Model_Task_Arrival_Task_max_inter_arrival_valid_task_max_inter_arrival_time 
  Task inst_3
  inst_6 
  Job inst_10
  inst_13
  inst_17 
  arr_seq tsk
```
