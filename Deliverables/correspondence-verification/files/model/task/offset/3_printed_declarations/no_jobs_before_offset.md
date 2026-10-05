# `no_jobs_before_offset`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.offset.no_jobs_before_offset`
- Lean: `Prosa.Model.Task.Offset.no_jobs_before_offset`
- Certificate: `no_jobs_before_offset_correspondence`

## Official Rocq

```coq
no_jobs_before_offset :
forall {Task : TaskType},
TaskOffset Task -> forall {Job : JobType}, JobTask Job Task -> JobArrival Job -> Equality.sort Task -> Prop

no_jobs_before_offset is not universe polymorphic
Arguments no_jobs_before_offset {Task H Job H0 H1} tsk
no_jobs_before_offset is transparent
Expands to: Constant prosa.model.task.offset.no_jobs_before_offset
Declared in library prosa.model.task.offset, line 30, characters 13-34
@no_jobs_before_offset
     : forall Task : TaskType,
       TaskOffset Task ->
       forall Job : JobType, JobTask Job Task -> JobArrival Job -> Equality.sort Task -> Prop
```

Body:

```coq
no_jobs_before_offset =
fun (Task : TaskType) (H : TaskOffset Task) (Job : JobType) (H0 : JobTask Job Task) 
  (H1 : JobArrival Job) (tsk : Equality.sort Task) =>
forall j : Equality.sort Job,
@job_task Job Task H0 j = tsk -> is_true (@task_offset Task H tsk <= @job_arrival Job H1 j)
     : forall {Task : TaskType},
       TaskOffset Task ->
       forall {Job : JobType}, JobTask Job Task -> JobArrival Job -> Equality.sort Task -> Prop

Arguments no_jobs_before_offset {Task H Job H0 H1} tsk
```

## Lean

```lean
@Prosa.Model.Task.Offset.no_jobs_before_offset : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Behavior.Job.JobArrival Job] → Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Offset.no_jobs_before_offset.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] → [Prosa.Behavior.Job.JobArrival Job] → Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] tsk =>
  ∀ (j : Job),
    Prosa.Model.Task.Concept.job_task j = tsk →
      Prosa.Model.Task.Offset.task_offset tsk ≤ Prosa.Behavior.Job.job_arrival j
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Offset_no_jobs_before_offset
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Offset_no_jobs_before_offset@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
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
  (tsk : Task) =>
forall j : Job,
@eq Task
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_10 Task
     inst_3
     inst_13 j)
  tsk ->
LE_le_inst1 Prosa_Behavior_Time_instant instLENat
  (Prosa_Model_Task_Offset_TaskOffset_task_offset Task
     inst_3
     inst_6 tsk)
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_10
     inst_17 j)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Task -> SProp

Arguments Prosa_Model_Task_Offset_no_jobs_before_offset Task
  inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17 tsk
```
