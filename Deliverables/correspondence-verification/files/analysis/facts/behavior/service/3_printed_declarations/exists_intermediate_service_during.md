# `exists_intermediate_service_during`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.behavior.service.exists_intermediate_service_during`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.exists_intermediate_service_during`
- Certificate: `exists_intermediate_service_during_correspondence`

## Official Rocq

```coq
exists_intermediate_service_during :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t0 t1 t2 s : nat),
is_true (t0 <= t1 <= t2) ->
is_true (@service_during Job PState sched j t0 t1 <= s < @service_during Job PState sched j t0 t2) ->
exists t : nat, is_true (t1 <= t < t2) /\ @service_during Job PState sched j t0 t = s

exists_intermediate_service_during is not universe polymorphic
Arguments exists_intermediate_service_during {Job PState} H_unit_service sched j (t0 t1 t2 s)%nat_scope _ _
exists_intermediate_service_during is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.exists_intermediate_service_during
Declared in library prosa.analysis.facts.behavior.service, line 194, characters 14-48
@exists_intermediate_service_during
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall (sched : @schedule Job PState) (j : Equality.sort Job) (t0 t1 t2 s : nat),
       is_true (t0 <= t1 <= t2) ->
       is_true (@service_during Job PState sched j t0 t1 <= s < @service_during Job PState sched j t0 t2) ->
       exists t : nat, is_true (t1 <= t < t2) /\ @service_during Job PState sched j t0 t = s
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.exists_intermediate_service_during : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t0 t1 t2 s : ℕ),
      (decide (t0 ≤ t1) && decide (t1 ≤ t2)) = true →
        (decide (Prosa.Behavior.Service.service_during sched j t0 t1 ≤ s) &&
              decide (s < Prosa.Behavior.Service.service_during sched j t0 t2)) =
            true →
          ∃ t, (decide (t1 ≤ t) && decide (t < t2)) = true ∧ Prosa.Behavior.Service.service_during sched j t0 t = s
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_exists_intermediate_service_during
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t0 t1 t2 s : Nat),
       @eq Bool
         (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t0 t1) (Nat_decLe t0 t1))
            (Decidable_decide (LE_le_inst1 Nat instLENat t1 t2) (Nat_decLe t1 t2)))
         Bool_true ->
       @eq Bool
         (Bool_and
            (Decidable_decide
               (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                  (Prosa_Behavior_Service_service_during Job
                     inst_3 PState sched
                     j t0 t1)
                  s)
               (Nat_decLe
                  (Prosa_Behavior_Service_service_during Job
                     inst_3 PState sched
                     j t0 t1)
                  s))
            (Decidable_decide
               (LT_lt_inst1 Nat instLTNat s
                  (Prosa_Behavior_Service_service_during Job
                     inst_3 PState sched
                     j t0 t2))
               (Nat_decLt s
                  (Prosa_Behavior_Service_service_during Job
                     inst_3 PState sched
                     j t0 t2))))
         Bool_true ->
       Exists Nat
         (fun t : Nat =>
          And
            (@eq Bool
               (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
                  (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
               Bool_true)
            (@eq Prosa_Behavior_Job_work
               (Prosa_Behavior_Service_service_during Job
                  inst_3 PState sched j
                  t0 t)
               s))
```
