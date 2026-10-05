# `equal_prefix_implies_same_service_during`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.equal_prefix_implies_same_service_during`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.equal_prefix_implies_same_service_during`
- Certificate: `equal_prefix_implies_same_service_during_correspondence`

## Official Rocq

```coq
equal_prefix_implies_same_service_during :
forall {Job : JobType} {PState : ProcessorState Job} (sched1 sched2 : @schedule Job PState) (t1 t2 : nat),
(forall t : nat, is_true (t1 <= t < t2) -> sched1 t = sched2 t) ->
forall j : Equality.sort Job,
@service_during Job PState sched1 j t1 t2 = @service_during Job PState sched2 j t1 t2

equal_prefix_implies_same_service_during is not universe polymorphic
Arguments equal_prefix_implies_same_service_during {Job PState} sched1 sched2 (t1 t2)%nat_scope
  _%function_scope j
equal_prefix_implies_same_service_during is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.equal_prefix_implies_same_service_during
Declared in library prosa.analysis.facts.behavior.service, line 905, characters 12-52
@equal_prefix_implies_same_service_during
     : forall (Job : JobType) (PState : ProcessorState Job) (sched1 sched2 : @schedule Job PState)
         (t1 t2 : nat),
       (forall t : nat, is_true (t1 <= t < t2) -> sched1 t = sched2 t) ->
       forall j : Equality.sort Job,
       @service_during Job PState sched1 j t1 t2 = @service_during Job PState sched2 j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.equal_prefix_implies_same_service_during : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched1 sched2 : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : ℕ),
  (∀ (t : ℕ), (decide (t1 ≤ t) && decide (t < t2)) = true → sched1 t = sched2 t) →
    ∀ (j : Job),
      Prosa.Behavior.Service.service_during sched1 j t1 t2 = Prosa.Behavior.Service.service_during sched2 j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_equal_prefix_implies_same_service_during
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched1
          sched2 : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
         (t1 t2 : Nat),
       (forall t : Nat,
        @eq Bool
          (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
             (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
          Bool_true ->
        @eq
          (Prosa_Behavior_Schedule_ProcessorState_State Job
             inst_3 PState)
          (sched1 t) (sched2 t)) ->
       forall j : Job,
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched1 j t1 t2)
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched2 j t1 t2)
```
