# `trivial_swap`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.trivial_swap`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.trivial_swap`
- Certificate: `trivial_swap_correspondence`

## Official Rocq

```coq
trivial_swap :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t1 t2 : instant),
t1 = t2 -> forall t : instant, sched t = @swapped Job PState sched t1 t2 t

trivial_swap is not universe polymorphic
Arguments trivial_swap {Job PState} sched t1 t2 _ t
trivial_swap is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.trivial_swap
Declared in library prosa.analysis.facts.transform.swaps, line 26, characters 8-20
@trivial_swap
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t1 t2 : instant),
       t1 = t2 -> forall t : instant, sched t = @swapped Job PState sched t1 t2 t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.trivial_swap : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  (t1 t2 : Prosa.Behavior.Time.instant),
  t1 = t2 → ∀ (t : Prosa.Behavior.Time.instant), sched t = Prosa.Analysis.Transform.Swap.swapped sched t1 t2 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_trivial_swap
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Prosa_Behavior_Time_instant t1 t2 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State Job
            inst_3 PState)
         (sched t)
         (Prosa_Analysis_Transform_Swap_swapped Job
            inst_3 PState sched t1 t2 t)
```
