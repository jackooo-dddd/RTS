# `quiet_time_P`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.definitions.busy_interval.classical.quiet_time_P`
- Lean: `Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time_P`
- Certificate: `quiet_time_P_correspondence`

## Official Rocq

```coq
quiet_time_P :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job}
  (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H arr_seq ->
forall (sched : @schedule Job PState) {H1 : JLFP_policy Job} (j : Equality.sort Job) (t : instant),
reflect (@quiet_time Job H H0 PState arr_seq sched H1 j t)
  (@quiet_time_dec Job H0 PState arr_seq sched H1 j t)

quiet_time_P is not universe polymorphic
Arguments quiet_time_P {Job H H0 PState} arr_seq H_arrival_times_are_consistent sched {H1} j t
quiet_time_P is opaque
Expands to: Constant prosa.analysis.definitions.busy_interval.classical.quiet_time_P
Declared in library prosa.analysis.definitions.busy_interval.classical, line 72, characters 8-20
@quiet_time_P
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H arr_seq ->
       forall (sched : @schedule Job PState) (H1 : JLFP_policy Job) (j : Equality.sort Job) (t : instant),
       reflect (@quiet_time Job H H0 PState arr_seq sched H1 j t)
         (@quiet_time_dec Job H0 PState arr_seq sched H1 j t)
```

## Lean

```lean
@Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time_P : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) →
            Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
              (sched : Prosa.Behavior.Schedule.schedule PState) →
                [inst_3 : Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                  (j : Job) →
                    (t : Prosa.Behavior.Time.instant) →
                      Prosa.Analysis.Definitions.BusyInterval.Classical.BoolReflect
                        (Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time arr_seq sched j t)
                        (Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time_dec arr_seq sched j t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_P
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_6 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState)
         (inst_23 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_BusyInterval_Classical_BoolReflect
         (Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time Job
            inst_3
            inst_6
            inst_9 PState
            arr_seq sched
            inst_23 j t)
         (Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_dec Job
            inst_3
            inst_9 PState
            arr_seq sched
            inst_23 j t)
```
