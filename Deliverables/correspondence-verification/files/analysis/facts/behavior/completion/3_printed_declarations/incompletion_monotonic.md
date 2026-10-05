# `incompletion_monotonic`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.completion.incompletion_monotonic`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.incompletion_monotonic`
- Certificate: `incompletion_monotonic_correspondence`

## Official Rocq

```coq
incompletion_monotonic :
forall {Job : JobType} {H : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState)
  (j : Equality.sort Job) (t t' : nat),
is_true (t <= t') ->
is_true (~~ @completed_by Job PState sched H j t') -> is_true (~~ @completed_by Job PState sched H j t)

incompletion_monotonic is not universe polymorphic
Arguments incompletion_monotonic {Job H PState} sched j (t t')%nat_scope _ _
incompletion_monotonic is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.incompletion_monotonic
Declared in library prosa.analysis.facts.behavior.completion, line 35, characters 8-30
@incompletion_monotonic
     : forall (Job : JobType) (H : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t t' : nat),
       is_true (t <= t') ->
       is_true (~~ @completed_by Job PState sched H j t') ->
       is_true (~~ @completed_by Job PState sched H j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.incompletion_monotonic : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job)
  (t t' : ℕ),
  t ≤ t' →
    (!Prosa.Behavior.Service.completed_by sched j t') = true → (!Prosa.Behavior.Service.completed_by sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_incompletion_monotonic
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
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_6 j t'))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3 PState sched
               inst_6 j t))
         Bool_true
```
