# `constant_service_implies_not_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.constant_service_implies_not_scheduled`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.constant_service_implies_not_scheduled`
- Certificate: `constant_service_implies_not_scheduled_correspondence`

## Official Rocq

```coq
constant_service_implies_not_scheduled :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 : instant),
is_true (t1 <= t2) ->
@service Job PState sched j t1 = @service Job PState sched j t2 ->
forall t : nat, is_true (t1 <= t < t2) -> @service_at Job PState sched j t = 0

constant_service_implies_not_scheduled is not universe polymorphic
Arguments constant_service_implies_not_scheduled {Job PState} sched j t1 t2 H_t1_le_t2 
  H_same_service t%nat_scope _
constant_service_implies_not_scheduled is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.constant_service_implies_not_scheduled
Declared in library prosa.analysis.facts.behavior.service, line 592, characters 10-48
@constant_service_implies_not_scheduled
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 : instant),
       is_true (t1 <= t2) ->
       @service Job PState sched j t1 = @service Job PState sched j t2 ->
       forall t : nat, is_true (t1 <= t < t2) -> @service_at Job PState sched j t = 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.constant_service_implies_not_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
  t1 ≤ t2 →
    Prosa.Behavior.Service.service sched j t1 = Prosa.Behavior.Service.service sched j t2 →
      ∀ (t : ℕ), (decide (t1 ≤ t) && decide (t < t2)) = true → Prosa.Behavior.Service.service_at sched j t = 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_constant_service_implies_not_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t1)
         (Prosa_Behavior_Service_service Job
            inst_3 PState sched j t2) ->
       forall t : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (Prosa_Behavior_Service_service_at Job
            inst_3 PState sched j t)
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
```
