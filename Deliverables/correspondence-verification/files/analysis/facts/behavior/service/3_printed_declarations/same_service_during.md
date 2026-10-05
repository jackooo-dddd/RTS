# `same_service_during`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.same_service_during`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.same_service_during`
- Certificate: `same_service_during_correspondence`

## Official Rocq

```coq
same_service_during :
forall {Job : JobType} {PState : ProcessorState Job} (sched1 sched2 : @schedule Job PState) 
  (t1 t2 : instant) (j : Equality.sort Job),
(forall t : nat,
 is_true (t1 <= t < t2) -> @service_at Job PState sched1 j t = @service_at Job PState sched2 j t) ->
@service_during Job PState sched1 j t1 t2 = @service_during Job PState sched2 j t1 t2

same_service_during is not universe polymorphic
Arguments same_service_during {Job PState} sched1 sched2 t1 t2 j
  H_sched1_sched2_same_service_at%function_scope
same_service_during is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.same_service_during
Declared in library prosa.analysis.facts.behavior.service, line 896, characters 10-29
@same_service_during
     : forall (Job : JobType) (PState : ProcessorState Job) (sched1 sched2 : @schedule Job PState)
         (t1 t2 : instant) (j : Equality.sort Job),
       (forall t : nat,
        is_true (t1 <= t < t2) -> @service_at Job PState sched1 j t = @service_at Job PState sched2 j t) ->
       @service_during Job PState sched1 j t1 t2 = @service_during Job PState sched2 j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.same_service_during : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched1 sched2 : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
  (∀ (t : ℕ),
      (decide (t1 ≤ t) && decide (t < t2)) = true →
        Prosa.Behavior.Service.service_at sched1 j t = Prosa.Behavior.Service.service_at sched2 j t) →
    Prosa.Behavior.Service.service_during sched1 j t1 t2 = Prosa.Behavior.Service.service_during sched2 j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_same_service_during
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched1
          sched2 : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant) (j : Job),
       (forall t : Nat,
        @eq Bool
          (Bool_and
             (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
             (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
          Bool_true ->
        @eq Prosa_Behavior_Job_work
          (Prosa_Behavior_Service_service_at Job
             inst_3 PState sched1 j t)
          (Prosa_Behavior_Service_service_at Job
             inst_3 PState sched2 j t)) ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched1 j t1 t2)
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched2 j t1 t2)
```
