# `swap_job_scheduled_other_times`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.swap_job_scheduled_other_times`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_other_times`
- Certificate: `swap_job_scheduled_other_times_correspondence`

## Official Rocq

```coq
swap_job_scheduled_other_times :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t1 t2 : instant) (j : Equality.sort Job) (t : Equality.sort Datatypes_nat__canonical__eqtype_Equality),
is_true (t1 != t) ->
is_true (t2 != t) ->
@scheduled_at Job PState (@swapped Job PState sched t1 t2) j t = @scheduled_at Job PState sched j t

swap_job_scheduled_other_times is not universe polymorphic
Arguments swap_job_scheduled_other_times {Job PState} sched t1 t2 j t _ _
swap_job_scheduled_other_times is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swap_job_scheduled_other_times
Declared in library prosa.analysis.facts.transform.swaps, line 89, characters 8-38
@swap_job_scheduled_other_times
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t1 t2 : instant) (j : Equality.sort Job)
         (t : Equality.sort Datatypes_nat__canonical__eqtype_Equality),
       is_true (t1 != t) ->
       is_true (t2 != t) ->
       @scheduled_at Job PState (@swapped Job PState sched t1 t2) j t = @scheduled_at Job PState sched j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swap_job_scheduled_other_times : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant) (j : Job) (t : ℕ),
  decide (t1 ≠ t) = true →
    decide (t2 ≠ t) = true →
      Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t =
        Prosa.Behavior.Service.scheduled_at sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swap_job_scheduled_other_times
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant) (j : Job) (t : Nat),
       @eq Bool
         (Decidable_decide (Ne Prosa_Behavior_Time_instant t1 t)
            (instDecidableNot (@eq Prosa_Behavior_Time_instant t1 t) (instDecidableEqNat t1 t)))
         Bool_true ->
       @eq Bool
         (Decidable_decide (Ne Prosa_Behavior_Time_instant t2 t)
            (instDecidableNot (@eq Prosa_Behavior_Time_instant t2 t) (instDecidableEqNat t2 t)))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_swapped Job
               inst_3 PState sched t1 t2)
            j t)
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
```
