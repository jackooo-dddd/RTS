# `identical_prefix_inclusion`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.definitions.schedule_prefix.identical_prefix_inclusion`
- Lean: `Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix_inclusion`
- Certificate: `identical_prefix_inclusion_statement_correspondence`

## Official Rocq

```coq
identical_prefix_inclusion :
forall {Job : JobType} {PState : ProcessorState Job} (sched sched' : @schedule Job PState) (h h' : nat),
is_true (h' <= h) ->
@identical_prefix Job PState sched sched' h -> @identical_prefix Job PState sched sched' h'

identical_prefix_inclusion is not universe polymorphic
Arguments identical_prefix_inclusion {Job PState} sched sched' (h h')%nat_scope _ _ t _
identical_prefix_inclusion is opaque
Expands to: Constant prosa.analysis.definitions.schedule_prefix.identical_prefix_inclusion
Declared in library prosa.analysis.definitions.schedule_prefix, line 36, characters 7-33
@identical_prefix_inclusion
     : forall (Job : JobType) (PState : ProcessorState Job) (sched sched' : @schedule Job PState)
         (h h' : nat),
       is_true (h' <= h) ->
       @identical_prefix Job PState sched sched' h -> @identical_prefix Job PState sched sched' h'
```

## Lean

```lean
@Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix_inclusion : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched sched' : Prosa.Behavior.Schedule.schedule PState) (h h' : Prosa.Behavior.Time.instant),
  h' ≤ h →
    Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix sched sched' h →
      Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix sched sched' h'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix_inclusion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched
          sched' : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
         (h h' : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat h' h ->
       Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
         inst_3 PState sched sched' h ->
       Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
         inst_3 PState sched sched'
         h'
```
