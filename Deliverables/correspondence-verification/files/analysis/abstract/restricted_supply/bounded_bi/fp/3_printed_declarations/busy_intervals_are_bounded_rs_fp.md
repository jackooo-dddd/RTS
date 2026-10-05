# `busy_intervals_are_bounded_rs_fp`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.bounded_bi.fp.busy_intervals_are_bounded_rs_fp`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Fp.busy_intervals_are_bounded_rs_fp`
- Certificate: `busy_intervals_are_bounded_rs_fp_correspondence`

## Official Rocq

```coq
busy_intervals_are_bounded_rs_fp :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall (sched : @schedule Job PState) {JobReady0 : @JobReady Job PState H2 H1},
@work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched (@FP_to_JLFP Job Task H0 FP) ->
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall {H3 : JobPreemptable Job} {H4 : TaskMaxNonpreemptiveSegment Task},
@valid_preemption_model Job H2 H3 PState arr_seq sched ->
@valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H4 H3 PState arr_seq sched ->
@respects_FP_policy_at_preemption_point Task Job H0 H1 H2 PState H3 JobReady0 arr_seq sched FP ->
@definitions.work_conserving Job H1 H2 PState arr_seq sched
  (@rs_jlfp_interference Task Job H0 PState FP arr_seq sched)
  (@rs_jlfp_interfering_workload Task Job H0 H2 PState FP arr_seq sched) ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H0 arr_seq ts ->
@arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
forall {H5 : MaxArrivals Task},
@taskset_respects_max_arrivals Task Job H0 arr_seq H5 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall {SBF : SupplyBoundFunction},
@valid_busy_sbf Task Job H1 H2 H0 PState arr_seq sched (@FP_to_JLFP Job Task H0 FP) tsk SBF ->
unit_supply_bound_function SBF ->
forall L : duration,
is_true (0 < L) ->
is_true
  (@blocking_bound Task H4 FP ts tsk + @total_hep_request_bound_function_FP Task H H5 ts FP tsk L <= SBF L) ->
@busy_intervals_are_bounded_by Job Task H0 H1 H2 PState arr_seq sched tsk
  (@rs_jlfp_interference Task Job H0 PState FP arr_seq sched)
  (@rs_jlfp_interfering_workload Task Job H0 H2 PState FP arr_seq sched) L

busy_intervals_are_bounded_rs_fp is not universe polymorphic
Arguments busy_intervals_are_bounded_rs_fp {Task H Job H0 H1 H2 PState} H_uniprocessor_proc_model
  H_unit_supply_proc_model H_consumed_supply_proc_model {FP} H_priority_is_reflexive 
  H_priority_is_transitive arr_seq H_valid_arrival_sequence sched {JobReady0} H_job_ready 
  H_sched_valid {H3 H4} H_valid_preemption_model H_valid_model_with_bounded_nonpreemptive_segments
  H_respects_policy H_work_conserving ts%seq_scope H_all_jobs_from_taskset H_valid_job_cost 
  {H5} H_is_arrival_curve tsk H_tsk_in_ts {SBF} H_valid_SBF H_unit_SBF L H_L_positive 
  H_fixed_point j _ _ _
busy_intervals_are_bounded_rs_fp is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.bounded_bi.fp.busy_intervals_are_bounded_rs_fp
Declared in library prosa.analysis.abstract.restricted_supply.bounded_bi.fp, line 276, characters 8-40
@busy_intervals_are_bounded_rs_fp
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (sched : @schedule Job PState) (JobReady0 : @JobReady Job PState H2 H1),
       @work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched (@FP_to_JLFP Job Task H0 FP) ->
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall (H3 : JobPreemptable Job) (H4 : TaskMaxNonpreemptiveSegment Task),
       @valid_preemption_model Job H2 H3 PState arr_seq sched ->
       @valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H4 H3 PState arr_seq sched ->
       @respects_FP_policy_at_preemption_point Task Job H0 H1 H2 PState H3 JobReady0 arr_seq sched FP ->
       @definitions.work_conserving Job H1 H2 PState arr_seq sched
         (@rs_jlfp_interference Task Job H0 PState FP arr_seq sched)
         (@rs_jlfp_interfering_workload Task Job H0 H2 PState FP arr_seq sched) ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H0 arr_seq ts ->
       @arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
       forall H5 : MaxArrivals Task,
       @taskset_respects_max_arrivals Task Job H0 arr_seq H5 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall SBF : SupplyBoundFunction,
       @valid_busy_sbf Task Job H1 H2 H0 PState arr_seq sched (@FP_to_JLFP Job Task H0 FP) tsk SBF ->
       unit_supply_bound_function SBF ->
       forall L : duration,
       is_true (0 < L) ->
       is_true
         (@blocking_bound Task H4 FP ts tsk + @total_hep_request_bound_function_FP Task H H5 ts FP tsk L <=
          SBF L) ->
       @busy_intervals_are_bounded_by Job Task H0 H1 H2 PState arr_seq sched tsk
         (@rs_jlfp_interference Task Job H0 PState FP arr_seq sched)
         (@rs_jlfp_interfering_workload Task Job H0 H2 PState FP arr_seq sched) L
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Fp.busy_intervals_are_bounded_rs_fp : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
          Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
            Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
              ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
                Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
                  ∀ (sched : Prosa.Behavior.Schedule.schedule PState)
                    [inst_6 : Prosa.Behavior.Ready.JobReady Job PState],
                    Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                        ∀ [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
                          [inst_8 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task],
                          Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                            Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments
                                arr_seq sched →
                              Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched
                                  FP →
                                Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                                  ∀ (ts : List Task),
                                    Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                                      Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                                        ∀ [inst_9 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                                          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                                            ∀ (tsk : Task),
                                              decide (tsk ∈ ts) = true →
                                                ∀ (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
                                                  Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf arr_seq sched tsk
                                                      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                                    Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
                                                        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                                      ∀ (L : Prosa.Behavior.Time.duration),
                                                        0 < L →
                                                          Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts
                                                                  tsk +
                                                                Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP
                                                                  ts tsk L ≤
                                                              Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
                                                                L →
                                                            Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by
                                                              arr_seq sched tsk L
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_BoundedBi_Fp_busy_intervals_are_bounded_rs_fp
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
            inst_10 Task
            inst_3)
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
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_10,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_10
                    PState)
         (inst_59 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_10
            PState
            inst_20
            inst_17),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_10
         inst_17
         inst_20 PState
         inst_59 arr_seq
         sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_10 Task
            inst_3
            inst_13 FP) ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_10
         inst_17 PState
         sched inst_20
         inst_59 arr_seq ->
       forall
         (inst_79 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_10)
         (inst_82 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_3),
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_10
         inst_20
         inst_79 PState
         arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_3 Job
         inst_10
         inst_13
         inst_20
         inst_82
         inst_79 PState
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point Task
         inst_3 Job
         inst_10
         inst_13
         inst_17
         inst_20 PState
         inst_79
         inst_59 arr_seq
         sched FP ->
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_10
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
            inst_10
            PState arr_seq sched
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_10
               Task
               inst_3
               inst_13 FP))
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
            inst_10
            inst_20
            PState arr_seq sched
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_10
               Task
               inst_3
               inst_13 FP))
         inst_17
         inst_20 PState
         arr_seq sched ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_10
         inst_13 arr_seq
         ts ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_20 arr_seq ->
       forall
         inst_143 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq
         inst_143 ts ->
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
         arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_10 Task
            inst_3
            inst_13 FP)
         tsk (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       LE_le_inst1 Nat instLENat
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
               inst_3
               inst_82 FP
               ts tsk)
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
               inst_3
               inst_6
               inst_143
               ts FP tsk L))
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF L) ->
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
         inst_10
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interference Job
            inst_10
            PState arr_seq sched
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_10
               Task
               inst_3
               inst_13 FP))
         (Prosa_Analysis_Abstract_RestrictedSupply_IwInstantiation_rs_jlfp_interfering_workload Job
            inst_10
            inst_20
            PState arr_seq sched
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_10
               Task
               inst_3
               inst_13 FP))
         inst_17
         inst_20 PState
         arr_seq sched Task
         inst_3
         inst_13 tsk L
```
