# `service_at_of_others_invariant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.replace_at.service_at_of_others_invariant`
- Lean: `Prosa.Analysis.Facts.Transform.ReplaceAt.service_at_of_others_invariant`
- Certificate: `service_at_of_others_invariant_correspondence`

## Official Rocq

```coq
service_at_of_others_invariant :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t' : instant) (nstate : @State Job PState) (j : Equality.sort Job),
is_true (~~ @scheduled_in Job PState j (@replace_at Job PState sched t' nstate t')) ->
is_true (~~ @scheduled_in Job PState j (sched t')) ->
forall t : instant,
@service_at Job PState sched j t = @service_at Job PState (@replace_at Job PState sched t' nstate) j t

service_at_of_others_invariant is not universe polymorphic
Arguments service_at_of_others_invariant {Job PState} sched t' nstate j _ _ t
service_at_of_others_invariant is opaque
Expands to: Constant prosa.analysis.facts.transform.replace_at.service_at_of_others_invariant
Declared in library prosa.analysis.facts.transform.replace_at, line 94, characters 8-38
@service_at_of_others_invariant
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t' : instant) (nstate : @State Job PState) (j : Equality.sort Job),
       is_true (~~ @scheduled_in Job PState j (@replace_at Job PState sched t' nstate t')) ->
       is_true (~~ @scheduled_in Job PState j (sched t')) ->
       forall t : instant,
       @service_at Job PState sched j t = @service_at Job PState (@replace_at Job PState sched t' nstate) j t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.ReplaceAt.service_at_of_others_invariant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t' : Prosa.Behavior.Time.instant)
  (nstate : Prosa.Behavior.Schedule.ProcessorState.State Job) (j : Job),
  (!PState.scheduled_in j (Prosa.Analysis.Transform.Swap.replace_at sched t' nstate t')) = true →
    (!PState.scheduled_in j (sched t')) = true →
      ∀ (t : Prosa.Behavior.Time.instant),
        Prosa.Behavior.Service.service_at sched j t =
          Prosa.Behavior.Service.service_at (Prosa.Analysis.Transform.Swap.replace_at sched t' nstate) j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_ReplaceAt_service_at_of_others_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t' : Prosa_Behavior_Time_instant)
         (nstate : Prosa_Behavior_Schedule_ProcessorState_State Job
                     inst_3 PState)
         (j : Job),
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
               inst_3 PState j
               (Prosa_Analysis_Transform_Swap_replace_at Job
                  inst_3 PState sched
                  t' nstate t')))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Schedule_ProcessorState_scheduled_in Job
               inst_3 PState j
               (sched t')))
         Bool_true ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_replace_at Job
               inst_3 PState sched t'
               nstate)
            j t)
```
