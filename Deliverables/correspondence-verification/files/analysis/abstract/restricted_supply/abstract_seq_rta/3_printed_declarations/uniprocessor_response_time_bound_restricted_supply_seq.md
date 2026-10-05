# `uniprocessor_response_time_bound_restricted_supply_seq`

- Kind (Rocq): Theorem
- Rocq: `prosa.analysis.abstract.restricted_supply.abstract_seq_rta.uniprocessor_response_time_bound_restricted_supply_seq`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq`
- Certificate: `uniprocessor_response_time_bound_restricted_supply_seq_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_restricted_supply_seq :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {jc : JobCost Job} 
  {H3 : JobPreemptable Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H2 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H2 PState sched ->
@completed_jobs_dont_execute Job PState sched jc ->
@arrivals_have_valid_job_costs Task H Job H1 jc arr_seq ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_preemption_model Job jc H3 PState arr_seq sched ->
@valid_task_run_to_completion_threshold Task H Job H1 jc H3 H0 arr_seq tsk ->
forall {H4 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H4) ->
@taskset_respects_max_arrivals Task Job H1 arr_seq H4 ts ->
forall {H5 : Interference Job} {H6 : InterferingWorkload Job},
@work_conserving Job H2 jc PState arr_seq sched H5 H6 ->
@sequential_tasks Job Task H1 H2 jc PState arr_seq sched ->
@interference_and_workload_consistent_with_sequential_tasks Task Job H1 H2 jc PState arr_seq sched tsk H5 H6 ->
forall L : duration,
@busy_intervals_are_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H5 H6 L ->
forall {SBF : SupplyBoundFunction},
@valid_busy_sbf Task Job H2 jc H1 PState arr_seq sched tsk H5 H6 SBF ->
unit_supply_bound_function SBF ->
forall task_intra_IBF : duration -> duration -> duration,
@task_intra_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H5 H6 task_intra_IBF ->
forall R : duration,
(forall A : duration,
 is_in_search_space L
   (fun A0 Δ : duration =>
    @task_request_bound_function Task H H4 tsk (A0 + 1) - @task_cost Task H tsk + task_intra_IBF A0 Δ)
   A ->
 exists F : duration,
   is_true (F <= A + R) /\
   is_true
     (@task_request_bound_function Task H H4 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H0 tsk) +
      task_intra_IBF A F <= SBF F) /\
   is_true (SBF F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= SBF (A + R))) ->
@task_response_time_bound Task Job H2 jc H1 PState arr_seq sched tsk R

uniprocessor_response_time_bound_restricted_supply_seq is not universe polymorphic
Arguments uniprocessor_response_time_bound_restricted_supply_seq {Task H H0 Job H1 H2 jc H3 PState}
  H_uniprocessor_proc_model H_unit_supply_proc_model H_consumed_supply_proc_model 
  arr_seq H_valid_arrivals sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_valid_job_cost ts%seq_scope tsk H_tsk_in_ts H_valid_preemption_model
  H_valid_run_to_completion_threshold {H4} H_valid_arrival_curve H_is_arrival_curve 
  {H5 H6} H_work_conserving H_sequential_tasks H_interference_and_workload_consistent_with_sequential_tasks 
  L H_busy_interval_exists {SBF} H_valid_SBF H_unit_SBF task_intra_IBF%function_scope
  H_interference_inside_reservation_is_bounded R H_R_is_maximum_seq_rs%function_scope 
  j _ _
uniprocessor_response_time_bound_restricted_supply_seq is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.abstract_seq_rta.uniprocessor_response_time_bound_restricted_supply_seq
Declared in library prosa.analysis.abstract.restricted_supply.abstract_seq_rta, line 231, characters 10-64
@uniprocessor_response_time_bound_restricted_supply_seq
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (jc : JobCost Job)
         (H3 : JobPreemptable Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H2 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H2 PState sched ->
       @completed_jobs_dont_execute Job PState sched jc ->
       @arrivals_have_valid_job_costs Task H Job H1 jc arr_seq ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_preemption_model Job jc H3 PState arr_seq sched ->
       @valid_task_run_to_completion_threshold Task H Job H1 jc H3 H0 arr_seq tsk ->
       forall H4 : MaxArrivals Task,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H4) ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq H4 ts ->
       forall (H5 : Interference Job) (H6 : InterferingWorkload Job),
       @work_conserving Job H2 jc PState arr_seq sched H5 H6 ->
       @sequential_tasks Job Task H1 H2 jc PState arr_seq sched ->
       @interference_and_workload_consistent_with_sequential_tasks Task Job H1 H2 jc PState arr_seq sched tsk
         H5 H6 ->
       forall L : duration,
       @busy_intervals_are_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H5 H6 L ->
       forall SBF : SupplyBoundFunction,
       @valid_busy_sbf Task Job H2 jc H1 PState arr_seq sched tsk H5 H6 SBF ->
       unit_supply_bound_function SBF ->
       forall task_intra_IBF : duration -> duration -> duration,
       @task_intra_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H5 H6 task_intra_IBF ->
       forall R : duration,
       (forall A : duration,
        is_in_search_space L
          (fun A0 Δ : duration =>
           @task_request_bound_function Task H H4 tsk (A0 + 1) - @task_cost Task H tsk + task_intra_IBF A0 Δ)
          A ->
        exists F : duration,
          is_true (F <= A + R) /\
          is_true
            (@task_request_bound_function Task H H4 tsk (A + 1) -
             (@task_cost Task H tsk - @task_rtct Task H0 tsk) + task_intra_IBF A F <= 
             SBF F) /\
          is_true (SBF F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= SBF (A + R))) ->
       @task_response_time_bound Task Job H2 jc H1 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [jc : Prosa.Behavior.Job.JobCost Job] [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
          Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
            ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
              Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
                Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                  Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                      ∀ (ts : List Task) (tsk : Task),
                        decide (tsk ∈ ts) = true →
                          Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                            Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
                              ∀ [inst_7 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                                Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                                    Prosa.Model.Task.Arrival.Curves.max_arrivals →
                                  Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                                    ∀ [inst_8 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                                      [inst_9 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                                      Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                                        Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                                          Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks
                                              arr_seq sched tsk →
                                            ∀ (L : Prosa.Behavior.Time.duration),
                                              Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq
                                                  sched tsk L →
                                                ∀ (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
                                                  Prosa.Analysis.Abstract.RestrictedSupply.BusySbf.valid_busy_sbf
                                                      arr_seq sched tsk
                                                      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                                    Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
                                                        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                                      ∀
                                                        (task_intra_IBF :
                                                          Prosa.Behavior.Time.duration →
                                                            Prosa.Behavior.Time.duration →
                                                              Prosa.Behavior.Time.duration),
                                                        Prosa.Analysis.Abstract.IBF.SupplyTask.task_intra_interference_is_bounded_by
                                                            arr_seq sched tsk task_intra_IBF →
                                                          ∀ (R : Prosa.Behavior.Time.duration),
                                                            (∀ (A : Prosa.Behavior.Time.duration),
                                                                Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                                                                    (fun A0 Δ =>
                                                                      Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                                            tsk (A0 + 1) -
                                                                          Prosa.Model.Task.Concept.task_cost tsk +
                                                                        task_intra_IBF A0 Δ)
                                                                    A →
                                                                  ∃ F ≤ A + R,
                                                                    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                                              tsk (A + 1) -
                                                                            (Prosa.Model.Task.Concept.task_cost tsk -
                                                                              Prosa.Model.Task.Preemption.Parameters.task_rtct
                                                                                tsk) +
                                                                          task_intra_IBF A F ≤
                                                                        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
                                                                          F ∧
                                                                      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
                                                                            F +
                                                                          (Prosa.Model.Task.Concept.task_cost tsk -
                                                                            Prosa.Model.Task.Preemption.Parameters.task_rtct
                                                                              tsk) ≤
                                                                        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
                                                                          (A + R)) →
                                                              Prosa.Analysis.Definitions.Schedulability.task_response_time_bound
                                                                arr_seq sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_AbstractSeqRta_uniprocessor_response_time_bound_restricted_supply_seq
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
         (jc : Prosa_Behavior_Job_JobCost Job
                 inst_7)
         (inst_25 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_20
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
         inst_20 PState
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_7 PState
         sched jc ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_16 jc
         arr_seq ->
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
         inst_7 jc
         inst_25 PState
         arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_16 jc
         inst_25
         inst_13
         arr_seq tsk ->
       forall
         inst_96 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_96) ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_16
         arr_seq
         inst_96 ts ->
       forall
         (inst_109 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_112 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         inst_109
         inst_112
         inst_20 jc
         PState arr_seq sched ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_16
         inst_20 jc
         PState arr_seq sched ->
       Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_16
         inst_20 jc
         PState arr_seq sched tsk
         inst_109
         inst_112 ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
         inst_7
         inst_109
         inst_112
         inst_20 jc
         PState arr_seq sched Task
         inst_3
         inst_16 tsk L ->
       forall SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction,
       Prosa_Analysis_Abstract_RestrictedSupply_BusySbf_valid_busy_sbf Task
         inst_3 Job
         inst_7
         inst_20 jc
         inst_16 PState
         arr_seq sched tsk
         inst_109
         inst_112
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall
         task_intra_IBF : Prosa_Behavior_Time_duration ->
                          Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_IBF_SupplyTask_task_intra_interference_is_bounded_by Job
         inst_7 Task
         inst_3
         inst_16
         inst_20 jc
         PState arr_seq sched tsk
         inst_109
         inst_112
         task_intra_IBF ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
          (fun A0 _UU0394_ : Prosa_Behavior_Time_duration =>
           HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
             (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                   inst_3
                   inst_10
                   inst_96
                   tsk
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                      A0 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (...))))
                (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                   inst_3
                   inst_10
                   tsk))
             (task_intra_IBF A0 _UU0394_))
          A ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat F
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A R))
             (And
                (LE_le_inst1 Nat instLENat
                   (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                      (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (...) (...) (...))
                      (task_intra_IBF A F))
                   (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F))
                (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                   (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_duration
                      Prosa_Behavior_Job_work (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                      (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF F)
                      (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                         Prosa_Behavior_Time_duration (...) (...) (...)))
                   (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                         Prosa_Behavior_Time_duration (...) A R)))))) ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_7
         inst_20 jc
         inst_16 PState
         arr_seq sched tsk R
```
