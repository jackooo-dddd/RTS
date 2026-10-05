# `cumulative_interfering_workload_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interfering_workload_split`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.cumulative_interfering_workload_split`
- Certificate: `cumulative_interfering_workload_split_correspondence`

## Official Rocq

```coq
cumulative_interfering_workload_split :
forall {Job : JobType} {H2 : JobCost Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) {JLFP : JLFP_policy Job} (j : Equality.sort Job) 
  (t1 t2 : nat),
@cumulative_interfering_workload Job (@rs_jlfp_interfering_workload Job H2 PState arr_seq sched JLFP) j t1 t2 =
@blackout_during Job PState sched t1 t2 +
@cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t2 +
@cumulative_other_hep_jobs_interfering_workload Job H2 arr_seq JLFP j t1 t2

cumulative_interfering_workload_split is not universe polymorphic
Arguments cumulative_interfering_workload_split {Job H2 PState} arr_seq sched {JLFP} j (t1 t2)%nat_scope
cumulative_interfering_workload_split is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interfering_workload_split
Declared in library prosa.analysis.abstract.restricted_supply.iw_instantiation, line 137, characters 8-45
@cumulative_interfering_workload_split
     : forall (Job : JobType) (H2 : JobCost Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (JLFP : JLFP_policy Job)
         (j : Equality.sort Job) (t1 t2 : nat),
       @cumulative_interfering_workload Job (@rs_jlfp_interfering_workload Job H2 PState arr_seq sched JLFP)
         j t1 t2 =
       @blackout_during Job PState sched t1 t2 +
       @cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t2 +
       @cumulative_other_hep_jobs_interfering_workload Job H2 arr_seq JLFP j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.cumulative_interfering_workload_split : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_2 : Prosa.Model.Priority.Definitions.JLFP_policy Job]
  (j : Job) (t1 t2 : ℕ),
  Prosa.Analysis.Abstract.Definitions.cumulative_interfering_workload j t1 t2 =
    Prosa.Model.Processor.Supply.blackout_during sched t1 t2 +
        Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion arr_seq sched j t1 t2 +
      Prosa.Analysis.Definitions.Interference.cumulative_other_hep_jobs_interfering_workload arr_seq j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_cumulative_interfering_workload_split
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7
                    PState)
         (inst_19 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
         (j : Job) (t1 t2 : Nat),
       @eq Nat
         (Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload Job
            inst_7
            (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
               inst_7
               inst_10
               PState arr_seq sched
               inst_19)
            j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
               (Prosa_Model_Processor_Supply_blackout_during Job
                  inst_7
                  PState sched t1 t2)
               (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
                  inst_7
                  PState arr_seq sched
                  (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
                     inst_7
                     inst_19)
                  j t1 t2))
            (Prosa_Analysis_Definitions_Interference_cumulative_other_hep_jobs_interfering_workload Job
               inst_7
               inst_10
               arr_seq
               inst_19
               j t1 t2))
```
