# `uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.ideal.edf.bounded_nps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments`
- Lean: `Prosa.Results.Rta.Ideal.Edf.BoundedNps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments`
- Certificate: `uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task}
  {H1 : TaskRunToCompletionThreshold Task} {H2 : TaskMaxNonpreemptiveSegment Task} 
  {Job : JobType} {H3 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
  (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
forall {H4 : JobPreemptable Job},
@valid_model_with_bounded_nonpreemptive_segments Task Job H3 Cost H2 H4 (ideal.processor_state Job) arr_seq
  sched ->
@work_conserving Job Arrival Cost (ideal.processor_state Job)
  (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost (ideal.processor_state Job) H4
  (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H0 Arrival H3)) ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H3 arr_seq ts ->
@arrivals_have_valid_job_costs Task H Job H3 Cost arr_seq ->
forall {H5 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
@taskset_respects_max_arrivals Task Job H3 arr_seq H5 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@valid_preemption_model Job Cost H4 (ideal.processor_state Job) arr_seq sched ->
@valid_task_run_to_completion_threshold Task H Job H3 Cost H4 H1 arr_seq tsk ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H5 ts L ->
forall R : duration,
(forall A : duration,
 is_true (@is_in_search_space Task H H0 ts H5 tsk L A) ->
 exists F : duration,
   is_true
     (@blocking_bound Task H H0 H2 ts H5 tsk A +
      (@task_request_bound_function Task H H5 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H1 tsk)) +
      @bound_on_athep_workload Task H H0 H5 ts tsk A (A + F) <= A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= R)) ->
@task_response_time_bound Task Job Arrival Cost H3 (ideal.processor_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments is not universe polymorphic
Arguments uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
  {Task H H0 H1 H2 Job H3 Arrival Cost} arr_seq H_valid_arrival_sequence sched H_sched_valid 
  {H4} H_valid_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy 
  ts%seq_scope H_all_jobs_from_taskset H_valid_job_cost {H5} H_valid_arrival_curve 
  H_is_arrival_curve tsk H_tsk_in_ts H_valid_preemption_model H_valid_run_to_completion_threshold 
  L H_L_positive H_fixed_point R H_R_is_maximum%function_scope j _ _
uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments is opaque
Expands to: Constant
            prosa.results.rta.ideal.edf.bounded_nps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
Declared in library prosa.results.rta.ideal.edf.bounded_nps, line 226, characters 12-84
@uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task)
         (H1 : TaskRunToCompletionThreshold Task) (H2 : TaskMaxNonpreemptiveSegment Task) 
         (Job : JobType) (H3 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
         (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
       forall H4 : JobPreemptable Job,
       @valid_model_with_bounded_nonpreemptive_segments Task Job H3 Cost H2 H4 (ideal.processor_state Job)
         arr_seq sched ->
       @work_conserving Job Arrival Cost (ideal.processor_state Job)
         (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost (ideal.processor_state Job) H4
         (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 Arrival H3)) ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H3 arr_seq ts ->
       @arrivals_have_valid_job_costs Task H Job H3 Cost arr_seq ->
       forall H5 : MaxArrivals Task,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
       @taskset_respects_max_arrivals Task Job H3 arr_seq H5 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       @valid_preemption_model Job Cost H4 (ideal.processor_state Job) arr_seq sched ->
       @valid_task_run_to_completion_threshold Task H Job H3 Cost H4 H1 arr_seq tsk ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H5 ts L ->
       forall R : duration,
       (forall A : duration,
        is_true (@is_in_search_space Task H H0 ts H5 tsk L A) ->
        exists F : duration,
          is_true
            (@blocking_bound Task H H0 H2 ts H5 tsk A +
             (@task_request_bound_function Task H H5 tsk (A + 1) -
              (@task_cost Task H tsk - @task_rtct Task H1 tsk)) +
             @bound_on_athep_workload Task H H0 H5 ts tsk A (A + F) <= A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H1 tsk) <= R)) ->
       @task_response_time_bound Task Job Arrival Cost H3 (ideal.processor_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Edf.BoundedNps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Concept.TaskDeadline Task]
  [inst_4 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_5 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_6 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_7 : Prosa.Behavior.Job.JobArrival Job]
  [inst_8 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        ∀ [inst_9 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
          Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched →
            Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
              Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                  (Prosa.Model.Priority.Edf.EDF Job) →
                ∀ (ts : List Task),
                  Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                      ∀ [inst_10 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                        Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                            Prosa.Model.Task.Arrival.Curves.max_arrivals →
                          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                            ∀ (tsk : Task),
                              decide (tsk ∈ ts) = true →
                                Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                                  Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq
                                      tsk →
                                    ∀ (L : Prosa.Behavior.Time.duration),
                                      0 < L →
                                        L =
                                            Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function
                                              ts L →
                                          ∀ (R : Prosa.Behavior.Time.duration),
                                            (∀ (A : Prosa.Behavior.Time.duration),
                                                Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space ts tsk L A =
                                                    true →
                                                  ∃ F,
                                                    Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk
                                                              A +
                                                            (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                                tsk (A + 1) -
                                                              (Prosa.Model.Task.Concept.task_cost tsk -
                                                                Prosa.Model.Task.Preemption.Parameters.task_rtct tsk)) +
                                                          Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload
                                                            ts tsk A (A + F) ≤
                                                        A + F ∧
                                                      F +
                                                          (Prosa.Model.Task.Concept.task_cost tsk -
                                                            Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                                                        R) →
                                              Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq
                                                sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Edf_BoundedNps_uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (inst_19 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_3)
         (inst_22 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_26 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_29 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_26 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_29
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_26
            inst_29)
         arr_seq ->
       forall
         inst_58 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7,
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments_inst8 Task
         inst_3 Job
         inst_7
         inst_22
         inst_29
         inst_19
         inst_58
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_7
         inst_26
         inst_29
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_26
            inst_29)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_7
         inst_26
         inst_29
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         inst_58
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_26
            inst_29)
         arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_7
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_7
               inst_3
               inst_13
               inst_26
               inst_22)) ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_22 arr_seq ts ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_22
         inst_29 arr_seq ->
       forall
         inst_111 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_111) ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_22 arr_seq
         inst_111 ts ->
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
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_7
         inst_29
         inst_58
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_22
         inst_29
         inst_58
         inst_16 arr_seq tsk ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_10
            inst_111 ts L) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space Task
             inst_3
             inst_10
             inst_13 ts
             inst_111 tsk L A)
          Bool_true ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Nat instLENat
                (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                   (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                      (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
                         inst_3
                         inst_10
                         inst_13
                         inst_19 ts
                         inst_111 tsk A)
                      (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                            inst_3
                            inst_10
                            inst_111 tsk
                            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                               Prosa_Behavior_Time_duration
                               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                               (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                         (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                            Prosa_Behavior_Time_duration
                            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                               inst_3
                               inst_10
                               tsk)
                            (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct
                               Task
                               inst_3
                               inst_16
                               tsk))))
                   (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
                      inst_3
                      inst_10
                      inst_13
                      inst_111 ts tsk A
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
                         inst_10 tsk)
                      (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                         inst_3
                         inst_16 tsk)))
                R))) ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8 Task
         inst_3 Job
         inst_7
         inst_26
         inst_29
         inst_22
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched tsk R
```
