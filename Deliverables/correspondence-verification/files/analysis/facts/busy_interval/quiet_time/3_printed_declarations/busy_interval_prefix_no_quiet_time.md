# `busy_interval_prefix_no_quiet_time`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.busy_interval.quiet_time.busy_interval_prefix_no_quiet_time`
- Lean: `Prosa.Analysis.Facts.BusyInterval.QuietTime.busy_interval_prefix_no_quiet_time`
- Certificate: `busy_interval_prefix_no_quiet_time_correspondence`

## Official Rocq

```coq
busy_interval_prefix_no_quiet_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JLFP_policy Job}
  {PState : ProcessorState Job} (sched : @schedule Job PState) (arr_seq : arrival_sequence Job)
  (j : Equality.sort Job) (t1 t2 : instant),
@busy_interval_prefix Job H H0 PState arr_seq sched H1 j t1 t2 ->
forall t : nat, is_true (t1 < t < t2) -> ~ @quiet_time Job H H0 PState arr_seq sched H1 j t

busy_interval_prefix_no_quiet_time is not universe polymorphic
Arguments busy_interval_prefix_no_quiet_time {Job H H0 H1 PState} sched arr_seq j t1 t2 _ t%nat_scope _ _
busy_interval_prefix_no_quiet_time is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.quiet_time.busy_interval_prefix_no_quiet_time
Declared in library prosa.analysis.facts.busy_interval.quiet_time, line 34, characters 7-41
@busy_interval_prefix_no_quiet_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JLFP_policy Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (arr_seq : arrival_sequence Job)
         (j : Equality.sort Job) (t1 t2 : instant),
       @busy_interval_prefix Job H H0 PState arr_seq sched H1 j t1 t2 ->
       forall t : nat, is_true (t1 < t < t2) -> ~ @quiet_time Job H H0 PState arr_seq sched H1 j t
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.QuietTime.busy_interval_prefix_no_quiet_time : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Priority.Definitions.JLFP_policy Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ (t : ℕ),
      (decide (t1 < t) && decide (t < t2)) = true →
        ¬Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_QuietTime_busy_interval_prefix_no_quiet_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_12 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_6
         inst_9 PState arr_seq
         sched inst_12 j t1 t2 ->
       forall t : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t) (Nat_decLt t1 t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       Not
         (Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
            inst_3
            inst_6
            inst_9 PState arr_seq
            sched inst_12 j t)
```
