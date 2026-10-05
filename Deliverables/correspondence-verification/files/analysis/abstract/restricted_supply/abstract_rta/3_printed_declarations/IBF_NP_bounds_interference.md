# `IBF_NP_bounds_interference`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_NP_bounds_interference`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.IBF_NP_bounds_interference`
- Certificate: `IBF_NP_bounds_interference_correspondence`

## Official Rocq

```coq
IBF_NP_bounds_interference :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} 
  {H4 : JobPreemptable Job} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@jobs_must_arrive_to_execute Job H2 PState sched ->
@completed_jobs_dont_execute Job PState sched H3 ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_preemption_model Job H3 H4 PState arr_seq sched ->
@valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
forall {H5 : Interference Job} {H6 : InterferingWorkload Job},
@work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
forall {SBF : SupplyBoundFunction},
@valid_busy_sbf Task Job H2 H3 H1 PState arr_seq sched tsk H5 H6 SBF ->
unit_supply_bound_function SBF ->
forall intra_IBF : duration -> duration -> duration,
@intra_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6 intra_IBF ->
@job_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6
  (fun F Δ : duration => F - @task_rtct Task H0 tsk + (Δ - SBF Δ - (F - SBF F)))
  (@relative_time_to_reach_rtct Task H0 Job H2 H3 PState sched tsk H5 H6
     (fun A Δ : duration => Δ - SBF Δ + intra_IBF A Δ))

IBF_NP_bounds_interference is not universe polymorphic
Arguments IBF_NP_bounds_interference {Task H H0 Job H1 H2 H3 H4 PState} H_unit_supply_proc_model
  H_consumed_supply_proc_model arr_seq sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  ts%seq_scope tsk H_tsk_in_ts H_valid_preemption_model H_valid_run_to_completion_threshold 
  {H5 H6} H_work_conserving {SBF} H_valid_SBF H_unit_SBF intra_IBF%function_scope
  H_intra_supply_interference_is_bounded t1 t2 Δ j _ _ _ _ _ X _
IBF_NP_bounds_interference is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.abstract_rta.IBF_NP_bounds_interference
Declared in library prosa.analysis.abstract.restricted_supply.abstract_rta, line 283, characters 8-34
@IBF_NP_bounds_interference
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job)
         (H4 : JobPreemptable Job) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @jobs_must_arrive_to_execute Job H2 PState sched ->
       @completed_jobs_dont_execute Job PState sched H3 ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_preemption_model Job H3 H4 PState arr_seq sched ->
       @valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
       forall (H5 : Interference Job) (H6 : InterferingWorkload Job),
       @work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
       forall SBF : SupplyBoundFunction,
       @valid_busy_sbf Task Job H2 H3 H1 PState arr_seq sched tsk H5 H6 SBF ->
       unit_supply_bound_function SBF ->
       forall intra_IBF : duration -> duration -> duration,
       @intra_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6 intra_IBF ->
       @job_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6
         (fun F Δ : duration => F - @task_rtct Task H0 tsk + (Δ - SBF Δ - (F - SBF F)))
         (@relative_time_to_reach_rtct Task H0 Job H2 H3 PState sched tsk H5 H6
            (fun A Δ : duration => Δ - SBF Δ + intra_IBF A Δ))
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.IBF_NP_bounds_interference : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
        (sched : Prosa.Behavior.Schedule.schedule PState),
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
            ∀ (ts : List Task) (tsk : Task),
              decide (tsk ∈ ts) = true →
                Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                  Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
                    ∀ [inst_8 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                      [inst_9 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                      Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                        ∀ (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
                          Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.valid_busy_sbf arr_seq sched tsk
                              Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                            Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
                                Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                              ∀
                                (intra_IBF :
                                  Prosa.Behavior.Time.duration →
                                    Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                                Prosa.Analysis.Abstract.IBF.Supply.intra_interference_is_bounded_by arr_seq sched tsk
                                    intra_IBF →
                                  Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched tsk
                                    (fun F Δ =>
                                      F - Prosa.Model.Task.Preemption.Parameters.task_rtct tsk +
                                        (Δ -
                                            Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ -
                                          (F -
                                            Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
                                              F)))
                                    (Prosa.Analysis.Abstract.AbstractRta.relative_time_to_reach_rtct sched tsk
                                      fun A Δ =>
                                      Δ - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ +
                                        intra_IBF A Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_AbstractRta_IBF_NP_bounds_interference
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_26 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7
                    PState),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_20 PState
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_7 PState
         sched inst_23 ->
       forall (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_7
         inst_23
         inst_26 PState
         arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_23
         inst_26
         inst_13 arr_seq
         tsk ->
       forall
         (inst_77 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_80 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         inst_77
         inst_80
         inst_20
         inst_23 PState
         arr_seq sched ->
       forall SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction,
       Prosa_Analysis_Abstract_RestrictedSupply_BusySbf_valid_busy_sbf Task
         inst_3 Job
         inst_7
         inst_20
         inst_23
         inst_16 PState
         arr_seq sched tsk
         inst_77
         inst_80
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall
         intra_IBF : Prosa_Behavior_Time_duration ->
                     Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_IBF_Supply_intra_interference_is_bounded_by Job
         inst_7 Task
         inst_3
         inst_16
         inst_20
         inst_23 PState
         arr_seq sched tsk
         inst_77
         inst_80 intra_IBF ->
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job
         inst_7
         inst_77
         inst_80
         inst_20
         inst_23 PState
         arr_seq sched Task
         inst_3
         inst_16 tsk
         (fun F _UU0394_ : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
            (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
               Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) F
               (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                  inst_3
                  inst_13
                  tsk))
            (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
               (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                  Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                  _UU0394_
                  (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_))
               (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                  Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) F
                  (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F))))
         (Prosa_Analysis_Abstract_AbstractRta_relative_time_to_reach_rtct Task
            inst_3
            inst_13 Job
            inst_7
            inst_20
            inst_23 PState
            sched tsk
            inst_77
            inst_80
            (fun A _UU0394_ : Prosa_Behavior_Time_duration =>
             HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
               (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                  Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                  _UU0394_
                  (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_))
               (intra_IBF A _UU0394_)))
```
