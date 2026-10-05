# `identical_prefix_completed_by`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.identical_prefix_completed_by`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.identical_prefix_completed_by`
- Certificate: `identical_prefix_completed_by_correspondence`

## Official Rocq

```coq
identical_prefix_completed_by :
forall {Job : JobType} {PState : ProcessorState Job} {jc : JobCost Job}
  (sched1 sched2 : @schedule Job PState) (h : instant),
@identical_prefix Job PState sched1 sched2 h ->
forall (j : Equality.sort Job) (t : nat),
is_true (t <= h) -> @completed_by Job PState sched1 jc j t = @completed_by Job PState sched2 jc j t

identical_prefix_completed_by is not universe polymorphic
Arguments identical_prefix_completed_by {Job PState jc} sched1 sched2 h _ j t%nat_scope _
identical_prefix_completed_by is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.identical_prefix_completed_by
Declared in library prosa.analysis.facts.behavior.completion, line 403, characters 8-37
@identical_prefix_completed_by
     : forall (Job : JobType) (PState : ProcessorState Job) (jc : JobCost Job)
         (sched1 sched2 : @schedule Job PState) (h : instant),
       @identical_prefix Job PState sched1 sched2 h ->
       forall (j : Equality.sort Job) (t : nat),
       is_true (t <= h) -> @completed_by Job PState sched1 jc j t = @completed_by Job PState sched2 jc j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.identical_prefix_completed_by : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job} [jc : Prosa.Behavior.Job.JobCost Job]
  (sched1 sched2 : Prosa.Behavior.Schedule.schedule PState) (h : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix sched1 sched2 h →
    ∀ (j : Job),
      ∀ t ≤ h, Prosa.Behavior.Service.completed_by sched1 j t = Prosa.Behavior.Service.completed_by sched2 j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_identical_prefix_completed_by
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (jc : Prosa_Behavior_Job_JobCost Job
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
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched1 jc j t)
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched2 jc j t)
```
