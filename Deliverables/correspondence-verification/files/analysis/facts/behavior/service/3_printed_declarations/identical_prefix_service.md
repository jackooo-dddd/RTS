# `identical_prefix_service`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.identical_prefix_service`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.identical_prefix_service`
- Certificate: `identical_prefix_service_correspondence`

## Official Rocq

```coq
identical_prefix_service :
forall {Job : JobType} {PState : ProcessorState Job} (sched1 sched2 : @schedule Job PState) (h : instant),
@identical_prefix Job PState sched1 sched2 h ->
forall j : Equality.sort Job, @service Job PState sched1 j h = @service Job PState sched2 j h

identical_prefix_service is not universe polymorphic
Arguments identical_prefix_service {Job PState} sched1 sched2 h _ j
identical_prefix_service is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.identical_prefix_service
Declared in library prosa.analysis.facts.behavior.service, line 916, characters 12-36
@identical_prefix_service
     : forall (Job : JobType) (PState : ProcessorState Job) (sched1 sched2 : @schedule Job PState)
         (h : instant),
       @identical_prefix Job PState sched1 sched2 h ->
       forall j : Equality.sort Job, @service Job PState sched1 j h = @service Job PState sched2 j h
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.identical_prefix_service : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched1 sched2 : Prosa.Behavior.Schedule.schedule PState) (h : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix sched1 sched2 h →
    ∀ (j : Job), Prosa.Behavior.Service.service sched1 j h = Prosa.Behavior.Service.service sched2 j h
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_identical_prefix_service
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched1
          sched2 : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
         (h : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
         inst_3 PState sched1 sched2 h ->
       forall j : Job,
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched1 j h)
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched2 j h)
```
