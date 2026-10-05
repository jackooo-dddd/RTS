# `schedule_respects_preemption_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.limited_preemptive.schedule_respects_preemption_model`
- Lean: `Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model`
- Certificate: `schedule_respects_preemption_model_correspondence`

## Official Rocq

```coq
schedule_respects_preemption_model :
forall {Job : JobType} {PState : ProcessorState Job},
JobPreemptable Job -> arrival_sequence Job -> @schedule Job PState -> Prop

schedule_respects_preemption_model is not universe polymorphic
Arguments schedule_respects_preemption_model {Job PState H} arr_seq sched
schedule_respects_preemption_model is transparent
Expands to: Constant prosa.model.schedule.limited_preemptive.schedule_respects_preemption_model
Declared in library prosa.model.schedule.limited_preemptive, line 28, characters 13-47
@schedule_respects_preemption_model
     : forall (Job : JobType) (PState : ProcessorState Job),
       JobPreemptable Job -> arrival_sequence Job -> @schedule Job PState -> Prop
```

Body:

```coq
schedule_respects_preemption_model =
fun (Job : JobType) (PState : ProcessorState Job) (H : JobPreemptable Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) =>
forall (j : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j ->
is_true (~~ @job_preemptable Job H j (@service Job PState sched j t)) ->
is_true (@scheduled_at Job PState sched j t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       JobPreemptable Job -> arrival_sequence Job -> @schedule Job PState -> Prop

Arguments schedule_respects_preemption_model {Job PState H} arr_seq sched
```

## Lean

```lean
@Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop
```

Body:

```lean
def Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] {PState} [Prosa.Model.Preemption.Parameter.JobPreemptable Job] arr_seq sched =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      (!Prosa.Model.Preemption.Parameter.job_preemptable j (Prosa.Behavior.Service.service sched j t)) = true →
        Prosa.Behavior.Service.scheduled_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (inst_8 : 
   Prosa_Model_Preemption_Parameter_JobPreemptable Job
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
forall (j : Job) (t : Prosa_Behavior_Time_instant),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j ->
@eq Bool
  (Bool_not
     (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
        inst_3
        inst_8 j
        (Prosa_Behavior_Service_service Job
           inst_3 PState sched j t)))
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j t)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model 
  Job inst_3 
  PState inst_8 
  arr_seq sched
```
