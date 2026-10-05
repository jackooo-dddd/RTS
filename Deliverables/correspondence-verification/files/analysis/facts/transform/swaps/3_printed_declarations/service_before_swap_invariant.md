# `service_before_swap_invariant`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.transform.swaps.service_before_swap_invariant`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.service_before_swap_invariant`
- Certificate: `service_before_swap_invariant_correspondence`

## Official Rocq

```coq
service_before_swap_invariant :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t1 t2 : instant),
is_true (t1 <= t2) ->
forall t : nat,
is_true (t <= t1) ->
forall j : Equality.sort Job,
@service Job PState sched j t = @service Job PState (@swapped Job PState sched t1 t2) j t

service_before_swap_invariant is not universe polymorphic
Arguments service_before_swap_invariant {Job PState} sched t1 t2 H_well_ordered t%nat_scope _ j
service_before_swap_invariant is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.service_before_swap_invariant
Declared in library prosa.analysis.facts.transform.swaps, line 215, characters 12-41
@service_before_swap_invariant
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t1 t2 : instant),
       is_true (t1 <= t2) ->
       forall t : nat,
       is_true (t <= t1) ->
       forall j : Equality.sort Job,
       @service Job PState sched j t = @service Job PState (@swapped Job PState sched t1 t2) j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.service_before_swap_invariant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    ∀ t ≤ t1,
      ∀ (j : Job),
        Prosa.Behavior.Service.service sched j t =
          Prosa.Behavior.Service.service (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_service_before_swap_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       forall t : Nat,
       LE_le_inst1 Nat instLENat t t1 ->
       forall j : Job,
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t)
         (Prosa_Behavior_Service_service Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_swapped Job
               inst_3 PState sched t1 t2)
            j t)
```
