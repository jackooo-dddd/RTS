# `trivial_swap_service_invariant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.trivial_swap_service_invariant`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.trivial_swap_service_invariant`
- Certificate: `trivial_swap_service_invariant_correspondence`

## Official Rocq

```coq
trivial_swap_service_invariant :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t1 t2 : instant),
t1 = t2 ->
forall (t : instant) (j : Equality.sort Job),
@service Job PState sched j t = @service Job PState (@swapped Job PState sched t1 t2) j t

trivial_swap_service_invariant is not universe polymorphic
Arguments trivial_swap_service_invariant {Job PState} sched t1 t2 _ t j
trivial_swap_service_invariant is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.trivial_swap_service_invariant
Declared in library prosa.analysis.facts.transform.swaps, line 39, characters 8-38
@trivial_swap_service_invariant
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t1 t2 : instant),
       t1 = t2 ->
       forall (t : instant) (j : Equality.sort Job),
       @service Job PState sched j t = @service Job PState (@swapped Job PState sched t1 t2) j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.trivial_swap_service_invariant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant),
  t1 = t2 →
    ∀ (t : Prosa.Behavior.Time.instant) (j : Job),
      Prosa.Behavior.Service.service sched j t =
        Prosa.Behavior.Service.service (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_trivial_swap_service_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant),
       @eq Prosa_Behavior_Time_instant t1 t2 ->
       forall (t : Prosa_Behavior_Time_instant) (j : Job),
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t)
         (Prosa_Behavior_Service_service Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_swapped Job
               inst_3 PState sched t1 t2)
            j t)
```
