# `service_split_at_point`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.service_split_at_point`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.service_split_at_point`
- Certificate: `service_split_at_point_correspondence`

## Official Rocq

```coq
service_split_at_point :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (j : Equality.sort Job) (t1 t2 t3 : nat),
is_true (t1 <= t2 < t3) ->
@service_during Job PState sched j t1 t2 + @service_at Job PState sched j t2 +
@service_during Job PState sched j t2.+1 t3 = @service_during Job PState sched j t1 t3

service_split_at_point is not universe polymorphic
Arguments service_split_at_point {Job PState} sched j (t1 t2 t3)%nat_scope _
service_split_at_point is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.service_split_at_point
Declared in library prosa.analysis.facts.behavior.service, line 113, characters 8-30
@service_split_at_point
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState)
         (j : Equality.sort Job) (t1 t2 t3 : nat),
       is_true (t1 <= t2 < t3) ->
       @service_during Job PState sched j t1 t2 + @service_at Job PState sched j t2 +
       @service_during Job PState sched j t2.+1 t3 = @service_during Job PState sched j t1 t3
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.service_split_at_point : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t1 t2 t3 : ℕ),
  (decide (t1 ≤ t2) && decide (t2 < t3)) = true →
    Prosa.Behavior.Service.service_during sched j t1 t2 + Prosa.Behavior.Service.service_at sched j t2 +
        Prosa.Behavior.Service.service_during sched j (t2 + 1) t3 =
      Prosa.Behavior.Service.service_during sched j t1 t3
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_service_split_at_point
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t1 t2 t3 : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t2) (Nat_decLe t1 t2))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t2 t3) (Nat_decLt t2 t3)))
         Bool_true ->
       @eq Prosa_Behavior_Job_work
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
               (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
               (Prosa_Behavior_Service_service_during Job
                  inst_3 PState sched j t1
                  t2)
               (Prosa_Behavior_Service_service_at Job
                  inst_3 PState sched j t2))
            (Prosa_Behavior_Service_service_during Job
               inst_3 PState sched j
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) t2
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
               t3))
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState sched j t1 t3)
```
