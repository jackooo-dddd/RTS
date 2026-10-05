# `busy_interval_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.busy_interval.classical.busy_interval_prefix`
- Lean: `Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix`
- Certificate: `busy_interval_prefix_correspondence`

## Official Rocq

```coq
busy_interval_prefix :
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> Prop

busy_interval_prefix is not universe polymorphic
Arguments busy_interval_prefix {Job H H0 PState} arr_seq sched {H1} j t1 t_busy
busy_interval_prefix is transparent
Expands to: Constant prosa.analysis.definitions.busy_interval.classical.busy_interval_prefix
Declared in library prosa.analysis.definitions.busy_interval.classical, line 47, characters 15-35
@busy_interval_prefix
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> Prop
```

Body:

```coq
busy_interval_prefix =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (H1 : JLFP_policy Job)
  (j : Equality.sort Job) (t1 t_busy : instant) =>
is_true (t1 < t_busy) /\
@quiet_time Job H H0 PState arr_seq sched H1 j t1 /\
(forall t : nat, is_true (t1 < t < t_busy) -> ~ @quiet_time Job H H0 PState arr_seq sched H1 j t) /\
is_true (t1 <= @job_arrival Job H j < t_busy)
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> instant -> Prop

Arguments busy_interval_prefix {Job H H0 PState} arr_seq sched {H1} j t1 t_busy
```

## Lean

```lean
@Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule PState →
              [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule PState →
              [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] j t1 t_busy =>
  t1 < t_busy ∧
    Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t1 ∧
      (∀ (t : Prosa.Behavior.Time.instant),
          (decide (t1 < t) && decide (t < t_busy)) = true →
            ¬Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t) ∧
        (decide (t1 ≤ Prosa.Behavior.Job.job_arrival j) && decide (Prosa.Behavior.Job.job_arrival j < t_busy)) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix
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
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix@{u_1 u_2 u_3 Lean.u_1+1.0
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
  (j : Job) (t1 t_busy : Prosa_Behavior_Time_instant) =>
And (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t_busy)
  (And
     (Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
        inst_3
        inst_6
        inst_9 PState arr_seq
        sched inst_18 j t1)
     (And
        (forall t : Prosa_Behavior_Time_instant,
         @eq Bool
           (Bool_and
              (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t) (Nat_decLt t1 t))
              (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t_busy)
                 (Nat_decLt t t_busy)))
           Bool_true ->
         Not
           (Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
              inst_3
              inst_6
              inst_9 PState
              arr_seq sched
              inst_18 j t))
        (@eq Bool
           (Bool_and
              (Decidable_decide
                 (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
                    (Prosa_Behavior_Job_JobArrival_job_arrival Job
                       inst_3
                       inst_6
                       j))
                 (Nat_decLe t1
                    (Prosa_Behavior_Job_JobArrival_job_arrival Job
                       inst_3
                       inst_6
                       j)))
              (Decidable_decide
                 (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
                    (Prosa_Behavior_Job_JobArrival_job_arrival Job
                       inst_3
                       inst_6
                       j)
                    t_busy)
                 (Nat_decLt
                    (Prosa_Behavior_Job_JobArrival_job_arrival Job
                       inst_3
                       inst_6
                       j)
                    t_busy)))
           Bool_true)))
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
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp

Arguments Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix 
  Job inst_3
  inst_6
  inst_9 
  PState arr_seq sched
  inst_18 
  j t1 t
```
