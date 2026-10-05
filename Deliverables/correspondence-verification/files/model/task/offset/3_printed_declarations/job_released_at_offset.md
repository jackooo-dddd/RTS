# `job_released_at_offset`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.offset.job_released_at_offset`
- Lean: `Prosa.Model.Task.Offset.job_released_at_offset`
- Certificate: `job_released_at_offset_correspondence`

## Official Rocq

```coq
job_released_at_offset :
forall {Task : TaskType},
TaskOffset Task ->
forall {Job : JobType},
JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

job_released_at_offset is not universe polymorphic
Arguments job_released_at_offset {Task H Job H0 H1} arr_seq tsk
job_released_at_offset is transparent
Expands to: Constant prosa.model.task.offset.job_released_at_offset
Declared in library prosa.model.task.offset, line 37, characters 13-35
@job_released_at_offset
     : forall Task : TaskType,
       TaskOffset Task ->
       forall Job : JobType,
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop
```

Body:

```coq
job_released_at_offset =
fun (Task : TaskType) (H : TaskOffset Task) (Job : JobType) (H0 : JobTask Job Task) 
  (H1 : JobArrival Job) (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) =>
exists j' : Equality.sort Job,
  @arrives_in Job arr_seq j' /\
  @job_task Job Task H0 j' = tsk /\ @job_arrival Job H1 j' = @task_offset Task H tsk
     : forall {Task : TaskType},
       TaskOffset Task ->
       forall {Job : JobType},
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Equality.sort Task -> Prop

Arguments job_released_at_offset {Task H Job H0 H1} arr_seq tsk
```

## Lean

```lean
@Prosa.Model.Task.Offset.job_released_at_offset : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Offset.job_released_at_offset.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] arr_seq tsk =>
  ∃ j',
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j' ∧
      Prosa.Model.Task.Concept.job_task j' = tsk ∧
        Prosa.Behavior.Job.job_arrival j' = Prosa.Model.Task.Offset.task_offset tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Offset_job_released_at_offset
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Offset_job_released_at_offset@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Offset_TaskOffset Task
                                                                    inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Model_Task_Concept_JobTask Job
                                                                     inst_10
                                                                     Task
                                                                     inst_3)
  (inst_17 : Prosa_Behavior_Job_JobArrival Job
                                                                     inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (tsk : Task) =>
Exists Job
  (fun j' : Job =>
   And
     (Prosa_Behavior_Arrival_sequence_arrives_in Job
        inst_10 arr_seq j')
     (And
        (@eq Task
           (Prosa_Model_Task_Concept_JobTask_job_task Job
              inst_10 Task
              inst_3
              inst_13 j')
           tsk)
        (@eq Prosa_Behavior_Time_instant
           (Prosa_Behavior_Job_JobArrival_job_arrival Job
              inst_10
              inst_17 j')
           (Prosa_Model_Task_Offset_TaskOffset_task_offset Task
              inst_3
              inst_6 tsk))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Task -> SProp

Arguments Prosa_Model_Task_Offset_job_released_at_offset Task
  inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17 arr_seq tsk
```
