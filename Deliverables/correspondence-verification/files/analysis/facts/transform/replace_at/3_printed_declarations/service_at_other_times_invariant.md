# `service_at_other_times_invariant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.replace_at.service_at_other_times_invariant`
- Lean: `Prosa.Analysis.Facts.Transform.ReplaceAt.service_at_other_times_invariant`
- Certificate: `service_at_other_times_invariant_correspondence`

## Official Rocq

```coq
service_at_other_times_invariant :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t' : instant) (nstate : @State Job PState) (t1 t2 : nat),
is_true (t2 <= t') \/ is_true (t' < t1) ->
forall j : Equality.sort Job,
@service_during Job PState sched j t1 t2 =
@service_during Job PState (@replace_at Job PState sched t' nstate) j t1 t2

service_at_other_times_invariant is not universe polymorphic
Arguments service_at_other_times_invariant {Job PState} sched t' nstate (t1 t2)%nat_scope _ j
service_at_other_times_invariant is opaque
Expands to: Constant prosa.analysis.facts.transform.replace_at.service_at_other_times_invariant
Declared in library prosa.analysis.facts.transform.replace_at, line 48, characters 8-40
@service_at_other_times_invariant
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t' : instant) (nstate : @State Job PState) (t1 t2 : nat),
       is_true (t2 <= t') \/ is_true (t' < t1) ->
       forall j : Equality.sort Job,
       @service_during Job PState sched j t1 t2 =
       @service_during Job PState (@replace_at Job PState sched t' nstate) j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.ReplaceAt.service_at_other_times_invariant : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t' : Prosa.Behavior.Time.instant)
  (nstate : Prosa.Behavior.Schedule.ProcessorState.State Job) (t1 t2 : ℕ),
  t2 ≤ t' ∨ t' < t1 →
    ∀ (j : Job),
      Prosa.Behavior.Service.service_during sched j t1 t2 =
        Prosa.Behavior.Service.service_during (Prosa.Analysis.Transform.Swap.replace_at sched t' nstate) j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_ReplaceAt_service_at_other_times_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t' : Prosa_Behavior_Time_instant)
         (nstate : Prosa_Behavior_Schedule_ProcessorState_State Job
                     inst_3 PState)
         (t1 t2 : Nat),
       Or (LE_le_inst1 Nat instLENat t2 t') (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t' t1) ->
       forall j : Job,
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1
            t2)
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState
            (Prosa_Analysis_Transform_Swap_replace_at Job
               inst_3 PState sched t'
               nstate)
            j t1 t2)
```
