# `prm_sbf_valid_aux_21`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_21`
- Lean: `Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_valid_aux_21`
- Certificate: `prm_sbf_valid_aux_21_correspondence`

## Official Rocq

```coq
prm_sbf_valid_aux_21 :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (Π : duration) (k1 k2 : nat) (q1 q2 : duration),
is_true (q1 < Π) ->
is_true (q2 < Π) ->
is_true (k1 < k2) ->
@supply_during Job PState sched (k1 * Π + q1) (k2 * Π + q2) =
@supply_during Job PState sched (k1 * Π + q1) ((k1 + 1) * Π) +
@supply_during Job PState sched ((k1 + 1) * Π) (k2 * Π) +
@supply_during Job PState sched (k2 * Π) (k2 * Π + q2)

prm_sbf_valid_aux_21 is not universe polymorphic
Arguments prm_sbf_valid_aux_21 {Job PState} sched Π (k1 k2)%nat_scope q1 q2 H_q1_small H_q2_small H_k1_lt_k2
prm_sbf_valid_aux_21 is opaque
Expands to: Constant prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid_aux_21
Declared in library prosa.analysis.facts.model.sbf.periodic, line 219, characters 10-30
@prm_sbf_valid_aux_21
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (Π : duration) (k1 k2 : nat) (q1 q2 : duration),
       is_true (q1 < Π) ->
       is_true (q2 < Π) ->
       is_true (k1 < k2) ->
       @supply_during Job PState sched (k1 * Π + q1) (k2 * Π + q2) =
       @supply_during Job PState sched (k1 * Π + q1) ((k1 + 1) * Π) +
       @supply_during Job PState sched ((k1 + 1) * Π) (k2 * Π) +
       @supply_during Job PState sched (k2 * Π) (k2 * Π + q2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_valid_aux_21 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (period : Prosa.Behavior.Time.duration) (k1 k2 : ℕ)
  (q1 q2 : Prosa.Behavior.Time.duration),
  q1 < period →
    q2 < period →
      k1 < k2 →
        Prosa.Model.Processor.Supply.supply_during sched (k1 * period + q1) (k2 * period + q2) =
          Prosa.Model.Processor.Supply.supply_during sched (k1 * period + q1) ((k1 + 1) * period) +
              Prosa.Model.Processor.Supply.supply_during sched ((k1 + 1) * period) (k2 * period) +
            Prosa.Model.Processor.Supply.supply_during sched (k2 * period) (k2 * period + q2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid_aux_21
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (period : Prosa_Behavior_Time_duration) (k1 k2 : Nat) (q1 q2 : Prosa_Behavior_Time_duration),
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat q1 period ->
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat q2 period ->
       LT_lt_inst1 Nat instLTNat k1 k2 ->
       @eq Prosa_Behavior_Job_work
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
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
               (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
               (Prosa_Model_Processor_Supply_supply_during Job
                  inst_3 PState sched
                  (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                     (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k1
                        period)
                     q1)
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat)
                     (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) k1
                        (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
                     period))
               (Prosa_Model_Processor_Supply_supply_during Job
                  inst_3 PState sched
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat)
                     (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) k1
                        (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
                     period)
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k2
                     period)))
            (Prosa_Model_Processor_Supply_supply_during Job
               inst_3 PState sched
               (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k2
                  period)
               (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                  (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat) k2
                     period)
                  q2)))
```
