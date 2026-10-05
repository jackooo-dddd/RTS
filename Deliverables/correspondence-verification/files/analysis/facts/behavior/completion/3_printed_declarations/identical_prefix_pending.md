# `identical_prefix_pending`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.completion.identical_prefix_pending`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.identical_prefix_pending`
- Certificate: `identical_prefix_pending_correspondence`

## Official Rocq

```coq
identical_prefix_pending :
forall {Job : JobType} {PState : ProcessorState Job} {jc : JobCost Job} {ja : JobArrival Job}
  (sched1 sched2 : @schedule Job PState) (h : instant),
@identical_prefix Job PState sched1 sched2 h ->
forall (j : Equality.sort Job) (t : nat),
is_true (t <= h) -> @pending Job PState sched1 jc ja j t = @pending Job PState sched2 jc ja j t

identical_prefix_pending is not universe polymorphic
Arguments identical_prefix_pending {Job PState jc ja} sched1 sched2 h _ j t%nat_scope _
identical_prefix_pending is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.identical_prefix_pending
Declared in library prosa.analysis.facts.behavior.completion, line 416, characters 12-36
@identical_prefix_pending
     : forall (Job : JobType) (PState : ProcessorState Job) (jc : JobCost Job) (ja : JobArrival Job)
         (sched1 sched2 : @schedule Job PState) (h : instant),
       @identical_prefix Job PState sched1 sched2 h ->
       forall (j : Equality.sort Job) (t : nat),
       is_true (t <= h) -> @pending Job PState sched1 jc ja j t = @pending Job PState sched2 jc ja j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.identical_prefix_pending : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job} [jc : Prosa.Behavior.Job.JobCost Job]
  [ja : Prosa.Behavior.Job.JobArrival Job] (sched1 sched2 : Prosa.Behavior.Schedule.schedule PState)
  (h : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix sched1 sched2 h →
    ∀ (j : Job), ∀ t ≤ h, Prosa.Behavior.Service.pending sched1 j t = Prosa.Behavior.Service.pending sched2 j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_identical_prefix_pending
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (jc : Prosa_Behavior_Job_JobCost Job
                 inst_3)
         (ja : Prosa_Behavior_Job_JobArrival Job
                 inst_3)
         (sched1
          sched2 : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
         (h : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
         inst_3 PState sched1 sched2 h ->
       forall (j : Job) (t : Nat),
       LE_le_inst1 Nat instLENat t h ->
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched1 jc ja
            j t)
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched2 jc ja
            j t)
```
