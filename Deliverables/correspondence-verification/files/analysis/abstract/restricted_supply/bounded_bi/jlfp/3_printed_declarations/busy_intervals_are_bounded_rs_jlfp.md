# `busy_intervals_are_bounded_rs_jlfp`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.busy_intervals_are_bounded_rs_jlfp`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Jlfp.busy_intervals_are_bounded_rs_jlfp`
- Certificate: `busy_intervals_are_bounded_rs_jlfp_correspondence`

## Official Rocq

```coq
busy_intervals_are_bounded_rs_jlfp :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall (sched : @schedule Job PState) {JobReady0 : @JobReady Job PState H2 H1},
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
@definitions.work_conserving Job H1 H2 PState arr_seq sched
  (@rs_jlfp_interference Job PState JLFP arr_seq sched)
  (@rs_jlfp_interfering_workload Job H2 PState JLFP arr_seq sched) ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H0 arr_seq ts ->
@arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
forall {H5 : MaxArrivals Task},
@taskset_respects_max_arrivals Task Job H0 arr_seq H5 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall {SBF : SupplyBoundFunction},
@valid_busy_sbf Task Job H1 H2 H0 PState arr_seq sched JLFP tsk SBF ->
unit_supply_bound_function SBF ->
forall blocking_bound : duration -> duration,
@service_inversion_is_bounded_by Task Job H0 H1 H2 PState arr_seq sched JLFP tsk blocking_bound ->
(forall A : duration, is_true (blocking_bound A <= blocking_bound 0)) ->
forall L : duration,
is_true (0 < L) ->
is_true (blocking_bound 0 + @total_request_bound_function Task H H5 ts L <= SBF L) ->
@busy_intervals_are_bounded_by Job Task H0 H1 H2 PState arr_seq sched tsk
  (@rs_jlfp_interference Job PState JLFP arr_seq sched)
  (@rs_jlfp_interfering_workload Job H2 PState JLFP arr_seq sched) L

busy_intervals_are_bounded_rs_jlfp is not universe polymorphic
Arguments busy_intervals_are_bounded_rs_jlfp {Task H Job H0 H1 H2 PState} H_uniprocessor_proc_model
  H_unit_supply_proc_model H_consumed_supply_proc_model {JLFP} H_priority_is_reflexive 
  arr_seq H_valid_arrival_sequence sched {JobReady0} H_sched_valid H_work_conserving 
  ts%seq_scope H_all_jobs_from_taskset H_valid_job_cost {H5} H_is_arrival_curve tsk 
  H_tsk_in_ts {SBF} H_valid_SBF H_unit_SBF blocking_bound%function_scope H_service_inversion_bounded
  H_blocking_bound_max%function_scope L H_L_positive H_fixed_point j _ _ _
busy_intervals_are_bounded_rs_jlfp is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp.busy_intervals_are_bounded_rs_jlfp
Declared in library prosa.analysis.abstract.restricted_supply.bounded_bi.jlfp, line 282, characters 8-42
@busy_intervals_are_bounded_rs_jlfp
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (sched : @schedule Job PState) (JobReady0 : @JobReady Job PState H2 H1),
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       @definitions.work_conserving Job H1 H2 PState arr_seq sched
         (@rs_jlfp_interference Job PState JLFP arr_seq sched)
         (@rs_jlfp_interfering_workload Job H2 PState JLFP arr_seq sched) ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H0 arr_seq ts ->
       @arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
       forall H5 : MaxArrivals Task,
       @taskset_respects_max_arrivals Task Job H0 arr_seq H5 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall SBF : SupplyBoundFunction,
       @valid_busy_sbf Task Job H1 H2 H0 PState arr_seq sched JLFP tsk SBF ->
       unit_supply_bound_function SBF ->
       forall blocking_bound : duration -> duration,
       @service_inversion_is_bounded_by Task Job H0 H1 H2 PState arr_seq sched JLFP tsk blocking_bound ->
       (forall A : duration, is_true (blocking_bound A <= blocking_bound 0)) ->
       forall L : duration,
       is_true (0 < L) ->
       is_true (blocking_bound 0 + @total_request_bound_function Task H H5 ts L <= SBF L) ->
       @busy_intervals_are_bounded_by Job Task H0 H1 H2 PState arr_seq sched tsk
         (@rs_jlfp_interference Job PState JLFP arr_seq sched)
         (@rs_jlfp_interfering_workload Job H2 PState JLFP arr_seq sched) L
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Jlfp.busy_intervals_are_bounded_rs_jlfp : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
          Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
                ∀ (sched : Prosa.Behavior.Schedule.schedule PState) [inst_6 : Prosa.Behavior.Ready.JobReady Job PState],
                  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                    Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                      ∀ (ts : List Task),
                        Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                          Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                            ∀ [inst_7 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                              Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                                ∀ (tsk : Task),
                                  decide (tsk ∈ ts) = true →
                                    ∀ (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
                                      Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf arr_seq sched tsk
                                          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                        Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
                                            Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                          ∀
                                            (blocking_bound :
                                              Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                                            Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_is_bounded_by
                                                arr_seq sched tsk blocking_bound →
                                              (∀ (A : Prosa.Behavior.Time.duration),
                                                  blocking_bound A ≤ blocking_bound 0) →
                                                ∀ (L : Prosa.Behavior.Time.duration),
                                                  0 < L →
                                                    blocking_bound 0 +
                                                          Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function
                                                            ts L ≤
                                                        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
                                                          L →
                                                      Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by
                                                        arr_seq sched tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Jlfp_busy_intervals_are_bounded_rs_jlfp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10
            Task inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_10),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_10 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_10 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_10 PState ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_10,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_10 JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_10,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17
         arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_10
                    PState)
         (inst_54 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_10
            PState
            inst_20
            inst_17),
       Prosa_Behavior_Ready_valid_schedule Job
         inst_10
         inst_17 PState
         sched inst_20
         inst_54
         arr_seq ->
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_10
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
            inst_10
            PState arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
            inst_10
            inst_20
            PState arr_seq sched JLFP)
         inst_17
         inst_20 PState
         arr_seq sched ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_10
         inst_13
         arr_seq ts ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_20
         arr_seq ->
       forall
         inst_100 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13
         arr_seq
         inst_100 ts ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction,
       Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf Task
         inst_3 Job
         inst_10
         inst_17
         inst_20
         inst_13 PState
         arr_seq sched JLFP tsk
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall blocking_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_is_bounded_by Task
         inst_3 Job
         inst_10
         inst_13
         inst_17
         inst_20 PState
         arr_seq sched JLFP tsk blocking_bound ->
       (forall A : Prosa_Behavior_Time_duration,
        LE_le_inst1 Prosa_Behavior_Time_duration instLENat (blocking_bound A)
          (blocking_bound (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))) ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (blocking_bound (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
               inst_3
               inst_6
               inst_100
               ts L))
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF L) ->
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
         inst_10
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
            inst_10
            PState arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
            inst_10
            inst_20
            PState arr_seq sched JLFP)
         inst_17
         inst_20 PState
         arr_seq sched Task
         inst_3
         inst_13 tsk L
```
