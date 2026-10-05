# `swap_other_times_invariant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.swap_other_times_invariant`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swap_other_times_invariant`
- Certificate: `swap_other_times_invariant_correspondence`

## Official Rocq

```coq
swap_other_times_invariant :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t1 t2 t : instant),
t <> t1 -> t <> t2 -> sched t = @swapped Job PState sched t1 t2 t

swap_other_times_invariant is not universe polymorphic
Arguments swap_other_times_invariant {Job PState} sched t1 t2 t _ _
swap_other_times_invariant is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swap_other_times_invariant
Declared in library prosa.analysis.facts.transform.swaps, line 51, characters 8-34
@swap_other_times_invariant
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (t1 t2 t : instant),
       t <> t1 -> t <> t2 -> sched t = @swapped Job PState sched t1 t2 t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swap_other_times_invariant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 t : Prosa.Behavior.Time.instant),
  t ≠ t1 → t ≠ t2 → sched t = Prosa.Analysis.Transform.Swap.swapped sched t1 t2 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swap_other_times_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 t : Prosa_Behavior_Time_instant),
       Ne Prosa_Behavior_Time_instant t t1 ->
       Ne Prosa_Behavior_Time_instant t t2 ->
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State Job
            inst_3 PState)
         (sched t)
         (Prosa_Analysis_Transform_Swap_swapped Job
            inst_3 PState sched t1 t2 t)
```
