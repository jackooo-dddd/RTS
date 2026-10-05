# `work_conserving`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.work_conserving.work_conserving`
- Lean: `Prosa.Model.Schedule.WorkConserving.work_conserving`
- Certificate: `work_conserving_correspondence`

## Official Rocq

```coq
work_conserving :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
@JobReady Job PState H0 H -> arrival_sequence Job -> @schedule Job PState -> Prop

work_conserving is not universe polymorphic
Arguments work_conserving {Job H H0 PState jr} arr_seq sched
work_conserving is transparent
Expands to: Constant prosa.model.schedule.work_conserving.work_conserving
Declared in library prosa.model.schedule.work_conserving, line 36, characters 13-28
@work_conserving
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job),
       @JobReady Job PState H0 H -> arrival_sequence Job -> @schedule Job PState -> Prop
```

Body:

```coq
work_conserving =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (jr : @JobReady Job PState H0 H) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) =>
forall (j : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j ->
is_true (@backlogged Job PState H0 H jr sched j t) ->
exists j_other : Equality.sort Job, is_true (@scheduled_at Job PState sched j_other t)
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
       @JobReady Job PState H0 H -> arrival_sequence Job -> @schedule Job PState -> Prop

Arguments work_conserving {Job H H0 PState jr} arr_seq sched
```

## Lean

```lean
@Prosa.Model.Schedule.WorkConserving.work_conserving : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop
def Prosa.Model.Schedule.WorkConserving.work_conserving.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Behavior.Ready.JobReady Job PState] arrSeq sched =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_in arrSeq j →
      Prosa.Behavior.Ready.backlogged sched j t = true →
        ∃ jOther, Prosa.Behavior.Service.scheduled_at sched jOther t = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_WorkConserving_work_conserving
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Model_Schedule_WorkConserving_work_conserving@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (inst_14 : Prosa_Behavior_Ready_JobReady
                                                                                Job
                                                                                inst_3
                                                                                PState
                                                                                inst_9
                                                                                inst_6)
  (arrSeq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
forall (j : Job) (t : Prosa_Behavior_Time_instant),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arrSeq j ->
@eq Bool
  (Prosa_Behavior_Ready_backlogged Job
     inst_3 PState
     inst_9
     inst_6
     inst_14 sched j t)
  Bool_true ->
Exists Job
  (fun jOther : Job =>
   Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched jOther t =
   Bool_true)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Model_Schedule_WorkConserving_work_conserving Job
  inst_3
  inst_6
  inst_9 PState
  inst_14 arrSeq 
  sched
```
