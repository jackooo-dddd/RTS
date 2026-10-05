# `uniprocessor_response_time_bound_seq`

- Kind (Rocq): Theorem
- Rocq: `prosa.analysis.abstract.ideal.abstract_seq_rta.uniprocessor_response_time_bound_seq`
- Lean: `Prosa.Analysis.Abstract.Ideal.AbstractSeqRta.uniprocessor_response_time_bound_seq`
- Certificate: `uniprocessor_response_time_bound_seq_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_seq :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} 
  {H4 : JobPreemptable Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_service_proc_model Job PState ->
@ideal_progress_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H2 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H2 PState sched ->
@completed_jobs_dont_execute Job PState sched H3 ->
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_preemption_model Job H3 H4 PState arr_seq sched ->
@valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
forall {H5 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
@taskset_respects_max_arrivals Task Job H1 arr_seq H5 ts ->
forall {H6 : Interference Job} {H7 : InterferingWorkload Job},
@work_conserving Job H2 H3 PState arr_seq sched H6 H7 ->
@sequential_tasks Job Task H1 H2 H3 PState arr_seq sched ->
@interference_and_workload_consistent_with_sequential_tasks Task Job H1 H2 H3 PState arr_seq sched tsk H6 H7 ->
forall L : duration,
@busy_intervals_are_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H6 H7 L ->
forall task_IBF : duration -> duration -> duration,
@task_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H6 H7 task_IBF ->
forall R : duration,
(forall A : duration,
 is_in_search_space L
   (fun A0 Δ : duration =>
    @task_request_bound_function Task H H5 tsk (A0 + 1) - @task_cost Task H tsk + task_IBF A0 Δ)
   A ->
 exists F : duration,
   is_true
     (@task_request_bound_function Task H H5 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H0 tsk) +
      task_IBF A (A + F) <= A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
@task_response_time_bound Task Job H2 H3 H1 PState arr_seq sched tsk R

uniprocessor_response_time_bound_seq is not universe polymorphic
Arguments uniprocessor_response_time_bound_seq {Task H H0 Job H1 H2 H3 H4 PState} 
  H_uniprocessor_proc_model H_unit_service_proc_model H_ideal_progress_proc_model 
  arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_valid_job_cost ts%seq_scope tsk H_tsk_in_ts H_valid_preemption_model
  H_valid_run_to_completion_threshold {H5} H_valid_arrival_curve H_is_arrival_curve 
  {H6 H7} H_work_conserving H_sequential_tasks H_interference_and_workload_consistent_with_sequential_tasks 
  L H_busy_interval_exists task_IBF%function_scope H_task_interference_is_bounded 
  R H_R_is_maximum_seq%function_scope j _ _
uniprocessor_response_time_bound_seq is opaque
Expands to: Constant prosa.analysis.abstract.ideal.abstract_seq_rta.uniprocessor_response_time_bound_seq
Declared in library prosa.analysis.abstract.ideal.abstract_seq_rta, line 205, characters 10-46
@uniprocessor_response_time_bound_seq
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job)
         (H4 : JobPreemptable Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_service_proc_model Job PState ->
       @ideal_progress_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H2 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H2 PState sched ->
       @completed_jobs_dont_execute Job PState sched H3 ->
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_preemption_model Job H3 H4 PState arr_seq sched ->
       @valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
       forall H5 : MaxArrivals Task,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq H5 ts ->
       forall (H6 : Interference Job) (H7 : InterferingWorkload Job),
       @work_conserving Job H2 H3 PState arr_seq sched H6 H7 ->
       @sequential_tasks Job Task H1 H2 H3 PState arr_seq sched ->
       @interference_and_workload_consistent_with_sequential_tasks Task Job H1 H2 H3 PState arr_seq sched tsk
         H6 H7 ->
       forall L : duration,
       @busy_intervals_are_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H6 H7 L ->
       forall task_IBF : duration -> duration -> duration,
       @task_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H6 H7 task_IBF ->
       forall R : duration,
       (forall A : duration,
        is_in_search_space L
          (fun A0 Δ : duration =>
           @task_request_bound_function Task H H5 tsk (A0 + 1) - @task_cost Task H tsk + task_IBF A0 Δ)
          A ->
        exists F : duration,
          is_true
            (@task_request_bound_function Task H H5 tsk (A + 1) -
             (@task_cost Task H tsk - @task_rtct Task H0 tsk) + task_IBF A (A + F) <= 
             A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
       @task_response_time_bound Task Job H2 H3 H1 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.AbstractSeqRta.uniprocessor_response_time_bound_seq : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
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
                              ∀ [inst_8 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                                Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                                    Prosa.Model.Task.Arrival.Curves.max_arrivals →
                                  Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                                    ∀ [inst_9 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                                      [inst_10 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                                      Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                                        Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                                          Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks
                                              arr_seq sched tsk →
                                            ∀ (L : Prosa.Behavior.Time.duration),
                                              Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq
                                                  sched tsk L →
                                                ∀
                                                  (task_IBF :
                                                    Prosa.Behavior.Time.duration →
                                                      Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                                                  Prosa.Analysis.Abstract.IBF.Task.task_interference_is_bounded_by
                                                      arr_seq sched tsk task_IBF →
                                                    ∀ (R : Prosa.Behavior.Time.duration),
                                                      (∀ (A : Prosa.Behavior.Time.duration),
                                                          Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                                                              (fun A0 Δ =>
                                                                Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                                      tsk (A0 + 1) -
                                                                    Prosa.Model.Task.Concept.task_cost tsk +
                                                                  task_IBF A0 Δ)
                                                              A →
                                                            ∃ F,
                                                              Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                                        tsk (A + 1) -
                                                                      (Prosa.Model.Task.Concept.task_cost tsk -
                                                                        Prosa.Model.Task.Preemption.Parameters.task_rtct
                                                                          tsk) +
                                                                    task_IBF A (A + F) ≤
                                                                  A + F ∧
                                                                F +
                                                                    (Prosa.Model.Task.Concept.task_cost tsk -
                                                                      Prosa.Model.Task.Preemption.Parameters.task_rtct
                                                                        tsk) ≤
                                                                  R) →
                                                        Prosa.Analysis.Definitions.Schedulability.task_response_time_bound
                                                          arr_seq sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_AbstractSeqRta_uniprocessor_response_time_bound_seq
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
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_7 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_20 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState sched
         arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_20 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_7 PState sched
         inst_23 ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_23 arr_seq ->
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
         inst_26 PState arr_seq
         sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_23
         inst_26
         inst_13 arr_seq tsk ->
       forall
         inst_97 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_97) ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_16 arr_seq
         inst_97 ts ->
       forall
         (inst_110 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_113 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         inst_110
         inst_113
         inst_20
         inst_23 PState arr_seq
         sched ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_16
         inst_20
         inst_23 PState arr_seq
         sched ->
       Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_16
         inst_20
         inst_23 PState arr_seq
         sched tsk inst_110
         inst_113 ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
         inst_7
         inst_110
         inst_113
         inst_20
         inst_23 PState arr_seq
         sched Task inst_3
         inst_16 tsk L ->
       forall
         task_IBF : Prosa_Behavior_Time_duration ->
                    Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_IBF_Task_task_interference_is_bounded_by Job
         inst_7 Task
         inst_3
         inst_16
         inst_20
         inst_23 PState arr_seq
         sched tsk inst_110
         inst_113 task_IBF ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
          (fun A0 _UU0394_ : Prosa_Behavior_Time_duration =>
           HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
             (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                   inst_3
                   inst_10
                   inst_97 tsk
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                      A0 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                   inst_3
                   inst_10 tsk))
             (task_IBF A0 _UU0394_))
          A ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Nat instLENat
                (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                   (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                      (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                         inst_3
                         inst_10
                         inst_97
                         tsk
                         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                            Prosa_Behavior_Time_duration
                            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 ...)))
                      (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                         Prosa_Behavior_Time_duration
                         (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                            inst_3
                            inst_10
                            tsk)
                         (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                            inst_3
                            inst_13
                            tsk)))
                   (task_IBF A
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                         Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) F
                   (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                      Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                      (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                         inst_3
                         inst_10
                         tsk)
                      (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                         inst_3
                         inst_13
                         tsk)))
                R))) ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_7
         inst_20
         inst_23
         inst_16 PState arr_seq
         sched tsk R
```
