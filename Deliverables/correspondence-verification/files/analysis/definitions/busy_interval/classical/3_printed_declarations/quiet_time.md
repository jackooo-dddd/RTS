# `quiet_time`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.busy_interval.classical.quiet_time`
- Lean: `Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time`
- Certificate: `quiet_time_correspondence`

## Official Rocq

```coq
quiet_time :
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> Prop

quiet_time is not universe polymorphic
Arguments quiet_time {Job H H0 PState} arr_seq sched {H1} j t
quiet_time is transparent
Expands to: Constant prosa.analysis.definitions.busy_interval.classical.quiet_time
Declared in library prosa.analysis.definitions.busy_interval.classical, line 35, characters 15-25
@quiet_time
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> Prop
```

Body:

```coq
quiet_time =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (H1 : JLFP_policy Job)
  (j : Equality.sort Job) (t : instant) =>
forall j_hp : Equality.sort Job,
@arrives_in Job arr_seq j_hp ->
is_true (@hep_job Job H1 j_hp j) ->
is_true (@arrived_before Job H j_hp t) -> is_true (@completed_by Job PState sched H0 j_hp t)
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> Prop

Arguments quiet_time {Job H H0 PState} arr_seq sched {H1} j t
```

## Lean

```lean
@Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule PState →
              [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule PState →
              [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] j t =>
  ∀ (j_hp : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j_hp →
      Prosa.Model.Priority.Definitions.hep_job j_hp j = true →
        Prosa.Behavior.Arrival_sequence.arrived_before j_hp t = true →
          Prosa.Behavior.Service.completed_by sched j_hp t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_18 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
forall j_hp : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j_hp ->
@eq Bool
  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
     inst_3
     inst_18 j_hp j)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Arrival_sequence_arrived_before Job
     inst_3
     inst_6 j_hp t)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_completed_by Job
     inst_3 PState sched
     inst_9 j_hp t)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> SProp

Arguments Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
  inst_3
  inst_6
  inst_9 
  PState arr_seq sched
  inst_18 
  j t
```
