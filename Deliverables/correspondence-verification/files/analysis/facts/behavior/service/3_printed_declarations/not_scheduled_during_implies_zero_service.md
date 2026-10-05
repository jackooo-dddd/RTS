# `not_scheduled_during_implies_zero_service`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.not_scheduled_during_implies_zero_service`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.not_scheduled_during_implies_zero_service`
- Certificate: `not_scheduled_during_implies_zero_service_correspondence`

## Official Rocq

```coq
not_scheduled_during_implies_zero_service :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : nat),
(forall t : nat, is_true (t1 <= t < t2) -> is_true (~~ @scheduled_at Job PState sched j t)) ->
@service_during Job PState sched j t1 t2 = 0

not_scheduled_during_implies_zero_service is not universe polymorphic
Arguments not_scheduled_during_implies_zero_service {Job PState} sched j (t1 t2)%nat_scope _%function_scope
not_scheduled_during_implies_zero_service is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.not_scheduled_during_implies_zero_service
Declared in library prosa.analysis.facts.behavior.service, line 323, characters 8-49
@not_scheduled_during_implies_zero_service
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : nat),
       (forall t : nat, is_true (t1 <= t < t2) -> is_true (~~ @scheduled_at Job PState sched j t)) ->
       @service_during Job PState sched j t1 t2 = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.not_scheduled_during_implies_zero_service : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : ℕ),
  (∀ (t : ℕ), (decide (t1 ≤ t) && decide (t < t2)) = true → (!Prosa.Behavior.Service.scheduled_at sched j t) = true) →
    Prosa.Behavior.Service.service_during sched j t1 t2 = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_not_scheduled_during_implies_zero_service
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Nat),
       (forall t : Nat,
        @eq Bool
          (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
             (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
          Bool_true ->
        @eq Bool
          (Bool_not
             (Prosa_Behavior_Service_scheduled_at Job
                inst_3 PState sched j t))
          Bool_true) ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t2)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
