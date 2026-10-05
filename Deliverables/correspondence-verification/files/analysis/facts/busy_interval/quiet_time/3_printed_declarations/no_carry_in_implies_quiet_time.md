# `no_carry_in_implies_quiet_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.quiet_time.no_carry_in_implies_quiet_time`
- Lean: `Prosa.Analysis.Facts.BusyInterval.QuietTime.no_carry_in_implies_quiet_time`
- Certificate: `no_carry_in_implies_quiet_time_correspondence`

## Official Rocq

```coq
no_carry_in_implies_quiet_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JLFP_policy Job}
  {PState : ProcessorState Job} (sched : @schedule Job PState) (arr_seq : arrival_sequence Job)
  (j : Equality.sort Job) (t : instant),
@no_carry_in Job H H0 arr_seq PState sched t -> @quiet_time Job H H0 PState arr_seq sched H1 j t

no_carry_in_implies_quiet_time is not universe polymorphic
Arguments no_carry_in_implies_quiet_time {Job H H0 H1 PState} sched arr_seq j t _ j_hp _ _ _
no_carry_in_implies_quiet_time is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.quiet_time.no_carry_in_implies_quiet_time
Declared in library prosa.analysis.facts.busy_interval.quiet_time, line 26, characters 8-38
@no_carry_in_implies_quiet_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JLFP_policy Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (arr_seq : arrival_sequence Job)
         (j : Equality.sort Job) (t : instant),
       @no_carry_in Job H H0 arr_seq PState sched t -> @quiet_time Job H H0 PState arr_seq sched H1 j t
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.QuietTime.no_carry_in_implies_quiet_time : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Priority.Definitions.JLFP_policy Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.CarryIn.no_carry_in arr_seq sched t →
    Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_QuietTime_no_carry_in_implies_quiet_time
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
         (j : Job) (t : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_CarryIn_no_carry_in Job
         inst_3
         inst_6
         inst_9 arr_seq PState
         sched t ->
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
         inst_3
         inst_6
         inst_9 PState arr_seq
         sched inst_12 j t
```
