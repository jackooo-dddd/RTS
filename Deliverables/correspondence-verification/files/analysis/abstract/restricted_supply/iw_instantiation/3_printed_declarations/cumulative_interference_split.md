# `cumulative_interference_split`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interference_split`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.cumulative_interference_split`
- Certificate: `cumulative_interference_split_correspondence`

## Official Rocq

```coq
cumulative_interference_split :
forall {Job : JobType} {H1 : JobArrival Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall (j : Equality.sort Job) (t1 t2 : nat),
@cumulative_interference Job (@rs_jlfp_interference Job PState arr_seq sched JLFP) j t1 t2 =
@blackout_during Job PState sched t1 t2 +
@cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t2 +
@cumulative_another_hep_job_interference Job PState arr_seq sched JLFP j t1 t2

cumulative_interference_split is not universe polymorphic
Arguments cumulative_interference_split {Job H1 PState} H_uniprocessor_proc_model
  H_consumed_supply_proc_model arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute {JLFP} H_priority_is_reflexive j (t1 t2)%nat_scope
cumulative_interference_split is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.iw_instantiation.cumulative_interference_split
Declared in library prosa.analysis.abstract.restricted_supply.iw_instantiation, line 103, characters 8-37
@cumulative_interference_split
     : forall (Job : JobType) (H1 : JobArrival Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall (j : Equality.sort Job) (t1 t2 : nat),
       @cumulative_interference Job (@rs_jlfp_interference Job PState arr_seq sched JLFP) j t1 t2 =
       @blackout_during Job PState sched t1 t2 +
       @cumulative_service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job JLFP) j t1 t2 +
       @cumulative_another_hep_job_interference Job PState arr_seq sched JLFP j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation.cumulative_interference_split : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
                  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                    ∀ (j : Job) (t1 t2 : ℕ),
                      Prosa.Analysis.Abstract.Definitions.cumulative_interference j t1 t2 =
                        Prosa.Model.Processor.Supply.blackout_during sched t1 t2 +
                            Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion arr_seq sched
                              j t1 t2 +
                          Prosa.Analysis.Definitions.Interference.cumulative_another_hep_job_interference arr_seq sched
                            j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_cumulative_interference_split
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10
         arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_10 PState
         sched ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall (j : Job) (t1 t2 : Nat),
       @eq Nat
         (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
            inst_7
            (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
               inst_7
               PState arr_seq sched JLFP)
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
                     JLFP)
                  j t1 t2))
            (Prosa_Analysis_Definitions_Interference_cumulative_another_hep_job_interference Job
               inst_7
               PState arr_seq sched JLFP j t1 t2))
```
