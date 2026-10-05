# `zero_is_quiet_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.quiet_time.zero_is_quiet_time`
- Lean: `Prosa.Analysis.Facts.BusyInterval.QuietTime.zero_is_quiet_time`
- Certificate: `zero_is_quiet_time_correspondence`

## Official Rocq

```coq
zero_is_quiet_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JLFP_policy Job}
  {PState : ProcessorState Job} (sched : @schedule Job PState) (arr_seq : arrival_sequence Job)
  (j : Equality.sort Job),
@quiet_time Job H H0 PState arr_seq sched H1 j 0

zero_is_quiet_time is not universe polymorphic
Arguments zero_is_quiet_time {Job H H0 H1 PState} sched arr_seq j j_hp _ _ _
zero_is_quiet_time is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.quiet_time.zero_is_quiet_time
Declared in library prosa.analysis.facts.busy_interval.quiet_time, line 20, characters 8-26
@zero_is_quiet_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JLFP_policy Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (arr_seq : arrival_sequence Job)
         (j : Equality.sort Job),
       @quiet_time Job H H0 PState arr_seq sched H1 j 0
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.QuietTime.zero_is_quiet_time : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Priority.Definitions.JLFP_policy Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (j : Job), Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_QuietTime_zero_is_quiet_time
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
         (j : Job),
       Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
         inst_3
         inst_6
         inst_9 PState arr_seq
         sched inst_12 j
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))
```
