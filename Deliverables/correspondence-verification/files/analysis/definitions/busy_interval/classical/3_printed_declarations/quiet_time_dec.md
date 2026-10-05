# `quiet_time_dec`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.busy_interval.classical.quiet_time_dec`
- Lean: `Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time_dec`
- Certificate: `quiet_time_dec_correspondence`

## Official Rocq

```coq
quiet_time_dec :
forall {Job : JobType},
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

quiet_time_dec is not universe polymorphic
Arguments quiet_time_dec {Job H0 PState} arr_seq sched {H1} j t
quiet_time_dec is transparent
Expands to: Constant prosa.analysis.definitions.busy_interval.classical.quiet_time_dec
Declared in library prosa.analysis.definitions.busy_interval.classical, line 66, characters 13-27
@quiet_time_dec
     : forall Job : JobType,
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
quiet_time_dec =
fun (Job : JobType) (H0 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H1 : JLFP_policy Job) (j : Equality.sort Job) (t : instant) =>
@all (Equality.sort Job)
  (fun j_hp : Equality.sort Job => @hep_job Job H1 j_hp j ==> @completed_by Job PState sched H0 j_hp t)
  (@arrivals_before Job arr_seq t)
     : forall {Job : JobType},
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

Arguments quiet_time_dec {Job H0 PState} arr_seq sched {H1} j t
```

## Lean

```lean
@Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time_dec : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule PState →
            [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time_dec.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobCost Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule PState →
            [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] j t =>
  (Prosa.Behavior.Arrival_sequence.arrivals_before arr_seq t).all fun j_hp =>
    !Prosa.Model.Priority.Definitions.hep_job j_hp j || Prosa.Behavior.Service.completed_by sched j_hp t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_dec
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
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
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_dec@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_15 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
List_all Job
  (Prosa_Behavior_Arrival_sequence_arrivals_before Job
     inst_3 arr_seq t)
  (fun j_hp : Job =>
   Bool_or
     (Bool_not
        (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
           inst_3
           inst_15 j_hp j))
     (Prosa_Behavior_Service_completed_by Job
        inst_3 PState sched
        inst_6 j_hp t))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
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
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_dec Job
  inst_3
  inst_6 
  PState arr_seq sched
  inst_15 
  j t
```
