# `preemption_time`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.preemption_time.preemption_time`
- Lean: `Prosa.Model.Schedule.PreemptionTime.preemption_time`
- Certificate: `preemption_time_correspondence`

## Official Rocq

```coq
preemption_time :
forall {Job : JobType},
JobPreemptable Job ->
arrival_sequence Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> instant -> bool

preemption_time is not universe polymorphic
Arguments preemption_time {Job H} arr_seq {PState} sched t
preemption_time is transparent
Expands to: Constant prosa.model.schedule.preemption_time.preemption_time
Declared in library prosa.model.schedule.preemption_time, line 35, characters 13-28
@preemption_time
     : forall Job : JobType,
       JobPreemptable Job ->
       arrival_sequence Job -> forall PState : ProcessorState Job, @schedule Job PState -> instant -> bool
```

Body:

```coq
preemption_time =
fun (Job : JobType) (H : JobPreemptable Job) (arr_seq : arrival_sequence Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) (t : instant) =>
match @scheduled_job_at Job PState arr_seq sched t with
| @Some _ j => @job_preemptable Job H j (@service Job PState sched j t)
| @None _ => true
end
     : forall {Job : JobType},
       JobPreemptable Job ->
       arrival_sequence Job -> forall {PState : ProcessorState Job}, @schedule Job PState -> instant -> bool

Arguments preemption_time {Job H} arr_seq {PState} sched t
```

## Lean

```lean
@Prosa.Model.Schedule.PreemptionTime.preemption_time : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Model.Schedule.PreemptionTime.preemption_time.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job] arr_seq {PState} sched t =>
  match Prosa.Model.Schedule.Scheduled.scheduled_job_at arr_seq sched t with
  | some j => Prosa.Model.Preemption.Parameter.job_preemptable j (Prosa.Behavior.Service.service sched j t)
  | none => true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_PreemptionTime_preemption_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Schedule_PreemptionTime_preemption_time@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                               Job
                                                                               inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (t : Prosa_Behavior_Time_instant) =>
Prosa_Model_Schedule_PreemptionTime_preemption_time_match_1 Job (fun _ : Option Job => Bool)
  (Prosa_Model_Schedule_Scheduled_scheduled_job_at Job
     inst_3 PState arr_seq sched t)
  (fun j : Job =>
   Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
     inst_3
     inst_6 j
     (Prosa_Behavior_Service_service Job
        inst_3 PState sched j t))
  (fun _ : Unit => Bool_true)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Schedule_PreemptionTime_preemption_time Job
  inst_3
  inst_6 arr_seq 
  PState sched t
```
