# `service_lt_workload_in_busy`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.bounded_bi.aux.service_lt_workload_in_busy`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary.service_lt_workload_in_busy`
- Certificate: `service_lt_workload_in_busy_correspondence`

## Official Rocq

```coq
service_lt_workload_in_busy :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
forall {JLFP : JLFP_policy Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall (sched : @schedule Job PState) {JobReady0 : @JobReady Job PState H2 H1},
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall j : Equality.sort Job,
is_true (@job_cost_positive Job H2 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
forall t : nat,
is_true (t1 < t < t2) ->
is_true
  (@service_of_hep_jobs Job PState arr_seq sched JLFP j t1 t <
   @workload_of_hep_jobs Job H2 arr_seq JLFP j t1 t)

service_lt_workload_in_busy is not universe polymorphic
Arguments service_lt_workload_in_busy {Job H1 H2 PState} H_unit_supply_proc_model 
  {JLFP} arr_seq H_valid_arrival_sequence sched {JobReady0} H_sched_valid j H_job_cost_positive 
  t1 t2 H_busy_prefix t%nat_scope _
service_lt_workload_in_busy is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.bounded_bi.aux.service_lt_workload_in_busy
Declared in library prosa.analysis.abstract.restricted_supply.bounded_bi.aux, line 96, characters 8-35
@service_lt_workload_in_busy
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       forall (JLFP : JLFP_policy Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (sched : @schedule Job PState) (JobReady0 : @JobReady Job PState H2 H1),
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall j : Equality.sort Job,
       is_true (@job_cost_positive Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
       forall t : nat,
       is_true (t1 < t < t2) ->
       is_true
         (@service_of_hep_jobs Job PState arr_seq sched JLFP j t1 t <
          @workload_of_hep_jobs Job H2 arr_seq JLFP j t1 t)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary.service_lt_workload_in_busy : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job]
      (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            ∀ (j : Job),
              Prosa.Model.Job.Properties.job_cost_positive j = true →
                ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                  Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
                    ∀ (t : ℕ),
                      (decide (t1 < t) && decide (t < t2)) = true →
                        Prosa.Model.Aggregate.ServiceOfJobs.service_of_hep_jobs arr_seq sched j t1 t <
                          Prosa.Model.Aggregate.Workload.workload_of_hep_jobs arr_seq j t1 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Auxiliary_service_lt_workload_in_busy
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
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3
         PState ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6
         arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState)
         (inst_30 : 
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
         inst_30
         arr_seq ->
       forall j : Job,
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9
            j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_6
         inst_9
         PState arr_seq sched JLFP j t1 t2 ->
       forall t : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t) (Nat_decLt t1 t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       LT_lt_inst1 Nat instLTNat
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_hep_jobs Job
            inst_3
            PState arr_seq sched JLFP j t1 t)
         (Prosa_Model_Aggregate_Workload_workload_of_hep_jobs Job
            inst_3
            inst_9
            arr_seq JLFP j t1 t)
```
