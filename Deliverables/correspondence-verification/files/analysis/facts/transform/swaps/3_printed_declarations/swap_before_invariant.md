# `swap_before_invariant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.swap_before_invariant`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swap_before_invariant`
- Certificate: `swap_before_invariant_correspondence`

## Official Rocq

```coq
swap_before_invariant :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t1 t2 : instant),
is_true (t1 <= t2) -> forall t : nat, is_true (t < t1) -> sched t = @swapped Job PState sched t1 t2 t

swap_before_invariant is not universe polymorphic
Arguments swap_before_invariant {Job PState} sched t1 t2 H_well_ordered t%nat_scope _
swap_before_invariant is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swap_before_invariant
Declared in library prosa.analysis.facts.transform.swaps, line 190, characters 8-29
@swap_before_invariant
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t1 t2 : instant),
       is_true (t1 <= t2) -> forall t : nat, is_true (t < t1) -> sched t = @swapped Job PState sched t1 t2 t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swap_before_invariant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 → ∀ t < t1, sched t = Prosa.Analysis.Transform.Swap.swapped sched t1 t2 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swap_before_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       forall t : Nat,
       LT_lt_inst1 Nat instLTNat t t1 ->
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State Job
            inst_3 PState)
         (sched t)
         (Prosa_Analysis_Transform_Swap_swapped Job
            inst_3 PState sched t1 t2 t)
```
