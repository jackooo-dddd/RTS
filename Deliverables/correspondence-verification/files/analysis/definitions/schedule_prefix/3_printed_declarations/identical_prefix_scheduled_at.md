# `identical_prefix_scheduled_at`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.definitions.schedule_prefix.identical_prefix_scheduled_at`
- Lean: `Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix_scheduled_at`
- Certificate: `identical_prefix_scheduled_at_statement_correspondence`

## Official Rocq

```coq
identical_prefix_scheduled_at :
forall {Job : JobType} {PState : ProcessorState Job} (sched sched' : @schedule Job PState) (h : instant),
@identical_prefix Job PState sched sched' h ->
forall (j : Equality.sort Job) (t : nat),
is_true (t < h) -> @scheduled_at Job PState sched j t = @scheduled_at Job PState sched' j t

identical_prefix_scheduled_at is not universe polymorphic
Arguments identical_prefix_scheduled_at {Job PState} sched sched' h _ j t%nat_scope _
identical_prefix_scheduled_at is opaque
Expands to: Constant prosa.analysis.definitions.schedule_prefix.identical_prefix_scheduled_at
Declared in library prosa.analysis.definitions.schedule_prefix, line 23, characters 7-36
@identical_prefix_scheduled_at
     : forall (Job : JobType) (PState : ProcessorState Job) (sched sched' : @schedule Job PState)
         (h : instant),
       @identical_prefix Job PState sched sched' h ->
       forall (j : Equality.sort Job) (t : nat),
       is_true (t < h) -> @scheduled_at Job PState sched j t = @scheduled_at Job PState sched' j t
```

## Lean

```lean
@Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix_scheduled_at : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched sched' : Prosa.Behavior.Schedule.schedule PState) (h : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix sched sched' h →
    ∀ (j : Job), ∀ t < h, Prosa.Behavior.Service.scheduled_at sched j t = Prosa.Behavior.Service.scheduled_at sched' j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix_scheduled_at
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched
          sched' : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
         (h : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
         inst_3 PState sched sched' h ->
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t h ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched' j t)
```
