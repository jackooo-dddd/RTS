# `cumulative_intra_interference_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_intra_interference_split`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.cumulative_intra_interference_split`
- Certificate: `cumulative_intra_interference_split_correspondence`

## Official Rocq

```coq
cumulative_intra_interference_split :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) {JLFP : JLFP_policy Job} (j : Equality.sort Job) 
  (t1 t2 : nat),
is_true
  (@cumul_cond_interference Job (@rs_jlfp_interference Job PState arr_seq sched JLFP)
     (fun=> [eta @has_supply Job PState sched]) j t1 t2 <=
   @cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t2 +
   @cumulative_another_hep_job_interference Job PState arr_seq sched JLFP j t1 t2)

cumulative_intra_interference_split is not universe polymorphic
Arguments cumulative_intra_interference_split {Job PState} arr_seq sched {JLFP} j (t1 t2)%nat_scope
cumulative_intra_interference_split is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_intra_interference_split
Declared in library prosa.analysis.abstract.restricted_supply.iw_instantiation, line 196, characters 8-43
@cumulative_intra_interference_split
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (JLFP : JLFP_policy Job) (j : Equality.sort Job) 
         (t1 t2 : nat),
       is_true
         (@cumul_cond_interference Job (@rs_jlfp_interference Job PState arr_seq sched JLFP)
            (fun=> [eta @has_supply Job PState sched]) j t1 t2 <=
          @cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t2 +
          @cumulative_another_hep_job_interference Job PState arr_seq sched JLFP j t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.cumulative_intra_interference_split : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  [inst_1 : Prosa.Model.Priority.Definitions.JLFP_policy Job] (j : Job) (t1 t2 : ℕ),
  Prosa.Analysis.Abstract.Definitions.cumul_cond_interference
      (fun x t => Prosa.Model.Processor.Supply.has_supply sched t) j t1 t2 ≤
    Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion arr_seq sched j t1 t2 +
      Prosa.Analysis.Definitions.Interference.cumulative_another_hep_job_interference arr_seq sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_cumulative_intra_interference_split
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7
                    PState)
         (inst_16 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
         (j : Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_7
            (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
               inst_7
               PState arr_seq sched
               inst_16)
            (fun (_ : Job) (t : Prosa_Behavior_Time_instant) =>
             Prosa_Model_Processor_Supply_has_supply Job
               inst_7
               PState sched t)
            j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
               inst_7
               PState arr_seq sched
               (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
                  inst_7
                  inst_16)
               j t1 t2)
            (Prosa_Analysis_Definitions_Interference_cumulative_another_hep_job_interference Job
               inst_7
               PState arr_seq sched
               inst_16
               j t1 t2))
```
