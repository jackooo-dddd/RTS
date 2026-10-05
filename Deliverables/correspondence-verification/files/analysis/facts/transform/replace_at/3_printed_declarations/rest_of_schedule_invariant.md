# `rest_of_schedule_invariant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.replace_at.rest_of_schedule_invariant`
- Lean: `Prosa.Analysis.Facts.Transform.ReplaceAt.rest_of_schedule_invariant`
- Certificate: `rest_of_schedule_invariant_correspondence`

## Official Rocq

```coq
rest_of_schedule_invariant :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t' : instant) (nstate : @State Job PState) (t : instant),
t <> t' -> @replace_at Job PState sched t' nstate t = sched t

rest_of_schedule_invariant is not universe polymorphic
Arguments rest_of_schedule_invariant {Job PState} sched t' nstate t _
rest_of_schedule_invariant is opaque
Expands to: Constant prosa.analysis.facts.transform.replace_at.rest_of_schedule_invariant
Declared in library prosa.analysis.facts.transform.replace_at, line 37, characters 8-34
@rest_of_schedule_invariant
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t' : instant) (nstate : @State Job PState) (t : instant),
       t <> t' -> @replace_at Job PState sched t' nstate t = sched t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.ReplaceAt.rest_of_schedule_invariant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t' : Prosa.Behavior.Time.instant)
  (nstate : Prosa.Behavior.Schedule.ProcessorState.State Job) (t : Prosa.Behavior.Time.instant),
  t ≠ t' → Prosa.Analysis.Transform.Swap.replace_at sched t' nstate t = sched t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_ReplaceAt_rest_of_schedule_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t' : Prosa_Behavior_Time_instant)
         (nstate : Prosa_Behavior_Schedule_ProcessorState_State Job
                     inst_3 PState)
         (t : Prosa_Behavior_Time_instant),
       Ne Prosa_Behavior_Time_instant t t' ->
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State Job
            inst_3 PState)
         (Prosa_Analysis_Transform_Swap_replace_at Job
            inst_3 PState sched t'
            nstate t)
         (sched t)
```
