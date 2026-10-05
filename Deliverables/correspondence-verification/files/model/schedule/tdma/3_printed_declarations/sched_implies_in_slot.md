# `sched_implies_in_slot`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.sched_implies_in_slot`
- Lean: `Prosa.Model.Schedule.Tdma.sched_implies_in_slot`
- Certificate: `sched_implies_in_slot_correspondence`

## Official Rocq

```coq
sched_implies_in_slot :
forall {Task : TaskType} {Job : JobType} {PState : ProcessorState Job},
JobTask Job Task ->
@schedule Job PState -> {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Job -> instant -> Prop

sched_implies_in_slot is not universe polymorphic
Arguments sched_implies_in_slot {Task Job PState H} sched ts {H0} j t
sched_implies_in_slot is transparent
Expands to: Constant prosa.model.schedule.tdma.sched_implies_in_slot
Declared in library prosa.model.schedule.tdma, line 141, characters 13-34
@sched_implies_in_slot
     : forall (Task : TaskType) (Job : JobType) (PState : ProcessorState Job),
       JobTask Job Task ->
       @schedule Job PState ->
       {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Job -> instant -> Prop
```

Body:

```coq
sched_implies_in_slot =
fun (Task : TaskType) (Job : JobType) (PState : ProcessorState Job) (H : JobTask Job Task)
  (sched : @schedule Job PState) (ts : {setEquality.sort Task}) (H0 : TDMAPolicy Task)
  (j : Equality.sort Job) (t : instant) =>
is_true (@scheduled_at Job PState sched j t) -> is_true (@job_in_time_slot Task Job H ts H0 j t)
     : forall {Task : TaskType} {Job : JobType} {PState : ProcessorState Job},
       JobTask Job Task ->
       @schedule Job PState ->
       {setEquality.sort Task} -> TDMAPolicy Task -> Equality.sort Job -> instant -> Prop

Arguments sched_implies_in_slot {Task Job PState H} sched ts {H0} j t
```

## Lean

```lean
@Prosa.Model.Schedule.Tdma.sched_implies_in_slot : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Schedule.schedule PState →
                Prosa.Util.Seqset.set Task → Job → Prosa.Behavior.Time.instant → Prop
def Prosa.Model.Schedule.Tdma.sched_implies_in_slot.{u_1, u_2, u_3, u_4} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Schedule.schedule PState →
                Prosa.Util.Seqset.set Task → Job → Prosa.Behavior.Time.instant → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Schedule.Tdma.TDMAPolicy Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] {PState} sched ts j t =>
  Prosa.Behavior.Service.scheduled_at sched j t = true → Prosa.Model.Schedule.Tdma.job_in_time_slot ts j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_sched_implies_in_slot
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Schedule_schedule Job inst_10
         PState ->
       Prosa_Util_Seqset_set Task inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> SProp
```

Body:

```coq
Prosa_Model_Schedule_Tdma_sched_implies_in_slot@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0
Lean.u_4+2.0} =
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
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_10)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_10 PState)
  (ts : Prosa_Util_Seqset_set Task inst_3) 
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job inst_10
     PState sched j t)
  Bool_true ->
@eq Bool
  (Prosa_Model_Schedule_Tdma_job_in_time_slot Task
     inst_3
     inst_6 Job
     inst_10
     inst_13 ts j t)
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Schedule_Tdma_TDMAPolicy Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Schedule_schedule Job inst_10
         PState ->
       Prosa_Util_Seqset_set Task inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> SProp

Arguments Prosa_Model_Schedule_Tdma_sched_implies_in_slot Task
  inst_3
  inst_6 Job
  inst_10
  inst_13 PState sched ts 
  j t
```
