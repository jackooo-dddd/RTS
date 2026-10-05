# `prm_sbf_valid_aux_23`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_23`
- Lean: `Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_valid_aux_23`
- Certificate: `prm_sbf_valid_aux_23_correspondence`

## Official Rocq

```coq
prm_sbf_valid_aux_23 :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (Π γ : duration),
@periodic_resource_model Job PState Π γ sched ->
forall (k1 k2 : nat) (q1 q2 : duration),
is_true (q1 < Π) ->
is_true (q2 < Π) ->
is_true (k1 < k2) -> is_true ((k2 - (k1 + 1)) * γ <= @supply_during Job PState sched ((k1 + 1) * Π) (k2 * Π))

prm_sbf_valid_aux_23 is not universe polymorphic
Arguments prm_sbf_valid_aux_23 {Job PState} sched Π γ H_periodic_resource_model (k1 k2)%nat_scope 
  q1 q2 H_q1_small H_q2_small H_k1_lt_k2
prm_sbf_valid_aux_23 is opaque
Expands to: Constant prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_23
Declared in library prosa.analysis.facts.model.sbf.periodic, line 271, characters 10-30
@prm_sbf_valid_aux_23
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (Π γ : duration),
       @periodic_resource_model Job PState Π γ sched ->
       forall (k1 k2 : nat) (q1 q2 : duration),
       is_true (q1 < Π) ->
       is_true (q2 < Π) ->
       is_true (k1 < k2) ->
       is_true ((k2 - (k1 + 1)) * γ <= @supply_during Job PState sched ((k1 + 1) * Π) (k2 * Π))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_valid_aux_23 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (period alloc : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model period alloc sched →
    ∀ (k1 k2 : ℕ) (q1 q2 : Prosa.Behavior.Time.duration),
      q1 < period →
        q2 < period →
          k1 < k2 →
            (k2 - (k1 + 1)) * alloc ≤ Prosa.Model.Processor.Supply.supply_during sched ((k1 + 1) * period) (k2 * period)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid_aux_23
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
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
       LE_le_inst1 Nat instLENat
         (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat)
            (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat) k2
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) k1
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
            alloc)
         (Prosa_Model_Processor_Supply_supply_during Job
            inst_3 PState sched
            (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat)
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) k1
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
               period)
            (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k2 period))
```
