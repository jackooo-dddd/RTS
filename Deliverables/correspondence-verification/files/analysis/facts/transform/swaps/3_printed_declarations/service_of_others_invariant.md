# `service_of_others_invariant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.service_of_others_invariant`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.service_of_others_invariant`
- Certificate: `service_of_others_invariant_correspondence`

## Official Rocq

```coq
service_of_others_invariant :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (t1 t2 : instant),
is_true (t1 <= t2) ->
forall (t : instant) (j : Equality.sort Job),
is_true (~~ @scheduled_in Job PState j (sched t1)) ->
is_true (~~ @scheduled_in Job PState j (sched t2)) ->
@service Job PState sched j t = @service Job PState (@swapped Job PState sched t1 t2) j t

service_of_others_invariant is not universe polymorphic
Arguments service_of_others_invariant {Job PState} sched t1 t2 H_well_ordered t j _ _
service_of_others_invariant is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.service_of_others_invariant
Declared in library prosa.analysis.facts.transform.swaps, line 249, characters 8-35
@service_of_others_invariant
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t1 t2 : instant),
       is_true (t1 <= t2) ->
       forall (t : instant) (j : Equality.sort Job),
       is_true (~~ @scheduled_in Job PState j (sched t1)) ->
       is_true (~~ @scheduled_in Job PState j (sched t2)) ->
       @service Job PState sched j t = @service Job PState (@swapped Job PState sched t1 t2) j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.service_of_others_invariant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    ∀ (t : Prosa.Behavior.Time.instant) (j : Job),
      (!PState.scheduled_in j (sched t1)) = true →
        (!PState.scheduled_in j (sched t2)) = true →
          Prosa.Behavior.Service.service sched j t =
            Prosa.Behavior.Service.service (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_service_of_others_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       forall (t : Prosa_Behavior_Time_instant) (j : Job),
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
               inst_3 PState j 
               (sched t1)))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
               inst_3 PState j 
               (sched t2)))
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t)
         (Prosa_Behavior_Service_service Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_swapped Job
               inst_3 PState sched t1 t2)
            j t)
```
