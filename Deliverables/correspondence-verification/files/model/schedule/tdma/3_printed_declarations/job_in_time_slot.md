# `job_in_time_slot`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.job_in_time_slot`
- Lean: `Prosa.Model.Schedule.Tdma.job_in_time_slot`
- Certificate: `job_in_time_slot_correspondence`

## Official Rocq

```coq
job_in_time_slot :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Job -> instant -> bool

job_in_time_slot is not universe polymorphic
Arguments job_in_time_slot {Task Job H} ts {H0} job t
job_in_time_slot is transparent
Expands to: Constant prosa.model.schedule.tdma.job_in_time_slot
Declared in library prosa.model.schedule.tdma, line 135, characters 13-29
@job_in_time_slot
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Job -> instant -> bool
```

Body:

```coq
job_in_time_slot =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (ts : {setEquality.sort Task})
  (H0 : TDMAPolicy Task) (job : Equality.sort Job) =>
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Job -> instant -> bool

Arguments job_in_time_slot {Task Job H} ts {H0} job t
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.job_in_time_slot : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            Prosa.Util.Seqset.set Task → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Model.Schedule.Tdma.job_in_time_slot.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            Prosa.Util.Seqset.set Task → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] ts j t =>
  Prosa.Model.Schedule.Tdma.task_in_time_slot ts (Prosa.Model.Task.Concept.job_task j) t
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_job_in_time_slot
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Schedule_Tdma_job_in_time_slot@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Schedule_Tdma_TDMAPolicy Task
                                                                      inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Model_Task_Concept_JobTask Job
                                                                       inst_10
                                                                       Task
                                                                       inst_3)
  (ts : Prosa_Util_Seqset_set Task inst_3) 
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Prosa_Model_Schedule_Tdma_task_in_time_slot Task
  inst_3
  inst_6 ts
  (Prosa_Model_Task_Concept_JobTask_job_task Job
     inst_10 Task
     inst_3
     inst_13 j)
  t
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Util_Seqset_set Task inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Schedule_Tdma_job_in_time_slot Task
  inst_3
  inst_6 Job
  inst_10
  inst_13 ts tsk t
```
