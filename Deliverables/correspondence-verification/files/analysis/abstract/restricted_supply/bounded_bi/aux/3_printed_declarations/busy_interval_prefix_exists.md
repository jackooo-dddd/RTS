# `busy_interval_prefix_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.bounded_bi.aux.busy_interval_prefix_exists`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary.busy_interval_prefix_exists`
- Certificate: `busy_interval_prefix_exists_correspondence`

## Official Rocq

```coq
busy_interval_prefix_exists :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall (sched : @schedule Job PState) {JobReady0 : @JobReady Job PState H2 H1},
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H2 j) ->
exists t1 : nat,
  is_true (t1 <= @job_arrival Job H1 j) /\
  @busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 (@job_arrival Job H1 j).+1

busy_interval_prefix_exists is not universe polymorphic
Arguments busy_interval_prefix_exists {Job H1 H2 PState} H_uniprocessor_proc_model 
  H_unit_supply_proc_model H_consumed_supply_proc_model {JLFP} H_priority_is_reflexive 
  arr_seq H_valid_arrival_sequence sched {JobReady0} H_sched_valid j H_j_arrives 
  H_job_cost_positive
busy_interval_prefix_exists is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.bounded_bi.aux.busy_interval_prefix_exists
Declared in library prosa.analysis.abstract.restricted_supply.bounded_bi.aux, line 77, characters 8-35
@busy_interval_prefix_exists
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (sched : @schedule Job PState) (JobReady0 : @JobReady Job PState H2 H1),
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H2 j) ->
       exists t1 : nat,
         is_true (t1 <= @job_arrival Job H1 j) /\
         @busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 (@job_arrival Job H1 j).+1
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary.busy_interval_prefix_exists : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
          Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
                ∀ (sched : Prosa.Behavior.Schedule.schedule PState) [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
                  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                    ∀ (j : Job),
                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                        Prosa.Model.Job.Properties.job_cost_positive j = true →
                          ∃ t1 ≤ Prosa.Behavior.Job.job_arrival j,
                            Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1
                              (Prosa.Behavior.Job.job_arrival j + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Auxiliary_busy_interval_prefix_exists
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3
         PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3
         PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_3
         PState ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3
         JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6
         arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState)
         (inst_43 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3
            PState
            inst_9
            inst_6),
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6
         PState sched
         inst_9
         inst_43
         arr_seq ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3
         arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9
            j)
         Bool_true ->
       Exists Nat
         (fun t1 : Nat =>
          And
            (LE_le_inst1 Nat instLENat t1
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_3
                  inst_6
                  j))
            (Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
               inst_3
               inst_6
               inst_9
               PState arr_seq sched JLFP j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_6
                     j)
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))))
```
