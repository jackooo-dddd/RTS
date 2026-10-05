# `cumulative_intra_interference_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_intra_interference_split`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.cumulative_intra_interference_split`
- Certificate: `cumulative_intra_interference_split_correspondence`

## Official Rocq

```coq
cumulative_intra_interference_split :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job}
  {JobReady0 : @JobReady Job PState H2 H1} (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  {JLFP : JLFP_policy Job} (j : Equality.sort Job) (t1 t2 : nat),
is_true
  (@cumul_cond_interference Job
     (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
     (fun=> [eta @has_supply Job PState sched]) j t1 t2 <=
   @cumulative_another_hep_job_interference Job PState arr_seq sched JLFP j t1 t2 +
   @cumulative_service_inversion Job H1 H2 PState JobReady0 arr_seq sched JLFP j t1 t2 +
   (fun (j0 : Equality.sort Job) (t3 t4 : instant) =>
    \sum_(t3 <= t < t4)
       nat_of_bool
         (@has_supply Job PState sched t &&
          ~~ @some_hep_job_ready Job H1 H2 PState JobReady0 arr_seq sched JLFP j0 t))
     j t1 t2)

cumulative_intra_interference_split is not universe polymorphic
Arguments cumulative_intra_interference_split {Job H1 H2 PState JobReady0} arr_seq 
  sched {JLFP} j (t1 t2)%nat_scope
cumulative_intra_interference_split is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_readiness.cumulative_intra_interference_split
Declared in library prosa.analysis.abstract.restricted_supply.iw_readiness, line 204, characters 8-43
@cumulative_intra_interference_split
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
         (JobReady0 : @JobReady Job PState H2 H1) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (JLFP : JLFP_policy Job) (j : Equality.sort Job) 
         (t1 t2 : nat),
       is_true
         (@cumul_cond_interference Job
            (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
            (fun=> [eta @has_supply Job PState sched]) j t1 t2 <=
          @cumulative_another_hep_job_interference Job PState arr_seq sched JLFP j t1 t2 +
          @cumulative_service_inversion Job H1 H2 PState JobReady0 arr_seq sched JLFP j t1 t2 +
          \sum_(t1 <= t < t2)
             nat_of_bool
               (@has_supply Job PState sched t &&
                ~~ @some_hep_job_ready Job H1 H2 PState JobReady0 arr_seq sched JLFP j t))
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.cumulative_intra_interference_split : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  [inst_3 : Prosa.Behavior.Ready.JobReady Job PState] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_4 : Prosa.Model.Priority.Definitions.JLFP_policy Job]
  (j : Job) (t1 t2 : ℕ),
  Prosa.Analysis.Abstract.Definitions.cumul_cond_interference
      (fun x t => Prosa.Model.Processor.Supply.has_supply sched t) j t1 t2 ≤
    Prosa.Analysis.Definitions.Interference.cumulative_another_hep_job_interference arr_seq sched j t1 t2 +
        Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.cumulative_service_inversion arr_seq sched j t1 t2 +
      ∑ t ∈ Finset.Ico t1 t2,
        (Prosa.Model.Processor.Supply.has_supply sched t &&
            !Prosa.Analysis.Definitions.ReadinessInterference.some_hep_job_ready arr_seq sched j t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_cumulative_intra_interference_split
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_13 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (inst_18 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_7 PState
            inst_13
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7
                    PState)
         (inst_26 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
         (j : Job) (t1 t2 : Nat),
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Abstract_Definitions_cumul_cond_interference Job
            inst_7
            (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference Job
               inst_7
               inst_10
               inst_13
               PState
               inst_18
               arr_seq sched
               inst_26)
            (fun (_ : Job) (t : Prosa_Behavior_Time_instant) =>
             Prosa_Model_Processor_Supply_has_supply Job
               inst_7
               PState sched t)
            j t1 t2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
               (Prosa_Analysis_Definitions_Interference_cumulative_another_hep_job_interference Job
                  inst_7
                  PState arr_seq sched
                  inst_26
                  j t1 t2)
               (Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_cumulative_service_inversion Job
                  inst_7
                  inst_10
                  inst_13
                  PState
                  inst_18
                  arr_seq sched
                  inst_26
                  j t1 t2))
            (List_foldr_inst3 Nat Nat Nat_add 0
               (List_map_inst3 Nat Nat
                  (fun t : Nat =>
                   Bool_toNat
                     (Bool_and
                        (Prosa_Model_Processor_Supply_has_supply Job
                           inst_7
                           PState sched t)
                        (Bool_not
                           (Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready Job
                              inst_7
                              inst_10
                              inst_13
                              PState
                              inst_18
                              arr_seq sched
                              inst_26
                              j t))))
                  (List_range' t1 (Nat_sub t2 t1) 1))))
```
