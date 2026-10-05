# `completion_monotonic`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.completion_monotonic`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic`
- Certificate: `completion_monotonic_correspondence`

## Official Rocq

```coq
completion_monotonic :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t t' : nat),
is_true (t <= t') ->
is_true (@completed_by Job PState sched H j t) -> is_true (@completed_by Job PState sched H j t')

completion_monotonic is not universe polymorphic
Arguments completion_monotonic {Job H PState} sched j (t t')%nat_scope _ _
completion_monotonic is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.completion_monotonic
Declared in library prosa.analysis.facts.behavior.completion, line 26, characters 8-28
@completion_monotonic
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t t' : nat),
       is_true (t <= t') ->
       is_true (@completed_by Job PState sched H j t) -> is_true (@completed_by Job PState sched H j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.completion_monotonic : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t t' : ℕ),
  t ≤ t' → Prosa.Behavior.Service.completed_by sched j t = true → Prosa.Behavior.Service.completed_by sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_completion_monotonic
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t t' : Nat),
       LE_le_inst1 Nat instLENat t t' ->
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched
            inst_6 j t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched
            inst_6 j t')
         Bool_true
```
