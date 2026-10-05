# `prm_sbf_valid_aux_2`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_2`
- Lean: `Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_valid_aux_2`
- Certificate: `prm_sbf_valid_aux_2_correspondence`

## Official Rocq

```coq
prm_sbf_valid_aux_2 :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
forall (sched : @schedule Job PState) (Π γ : duration),
@periodic_resource_model Job PState Π γ sched ->
forall (k1 k2 : nat) (q1 q2 : duration),
is_true (q1 < Π) ->
is_true (q2 < Π) ->
is_true (k1 < k2) ->
is_true
  (prm_sbf Π γ (k2 * Π + q2 - (k1 * Π + q1)) <= @supply_during Job PState sched (k1 * Π + q1) (k2 * Π + q2))

prm_sbf_valid_aux_2 is not universe polymorphic
Arguments prm_sbf_valid_aux_2 {Job PState} H_unit_supply_proc_model sched Π γ H_periodic_resource_model
  (k1 k2)%nat_scope q1 q2 H_q1_small H_q2_small H_k1_lt_k2
prm_sbf_valid_aux_2 is opaque
Expands to: Constant prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_2
Declared in library prosa.analysis.facts.model.sbf.periodic, line 323, characters 10-29
@prm_sbf_valid_aux_2
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       forall (sched : @schedule Job PState) (Π γ : duration),
       @periodic_resource_model Job PState Π γ sched ->
       forall (k1 k2 : nat) (q1 q2 : duration),
       is_true (q1 < Π) ->
       is_true (q2 < Π) ->
       is_true (k1 < k2) ->
       is_true
         (prm_sbf Π γ (k2 * Π + q2 - (k1 * Π + q1)) <=
          @supply_during Job PState sched (k1 * Π + q1) (k2 * Π + q2))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_valid_aux_2 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (period alloc : Prosa.Behavior.Time.duration),
      Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model period alloc sched →
        ∀ (k1 k2 : ℕ) (q1 q2 : Prosa.Behavior.Time.duration),
          q1 < period →
            q2 < period →
              k1 < k2 →
                Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf period alloc (k2 * period + q2 - (k1 * period + q1)) ≤
                  Prosa.Model.Processor.Supply.supply_during sched (k1 * period + q1) (k2 * period + q2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid_aux_2
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (period alloc : Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model Job
         inst_3 PState period alloc
         sched ->
       forall (k1 k2 : Nat) (q1 q2 : Prosa_Behavior_Time_duration),
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat q1 period ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat q2 period ->
       LT_lt_inst1 Nat instLTNat k1 k2 ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat
         (Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf period alloc
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k2
                     period)
                  q2)
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k1
                     period)
                  q1)))
         (Prosa_Model_Processor_Supply_supply_during Job
            inst_3 PState sched
            (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
               (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k1
                  period)
               q1)
            (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
               (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k2
                  period)
               q2))
```
