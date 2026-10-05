# `uniprocessor_response_time_bound_fp`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.ideal.fp.bounded_pi.uniprocessor_response_time_bound_fp`
- Lean: `Prosa.Results.Rta.Ideal.Fp.BoundedPi.uniprocessor_response_time_bound_fp`
- Certificate: `uniprocessor_response_time_bound_fp_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fp :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job}
  {H2 : JobPreemptable Job} {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job Arrival arr_seq ->
forall (sched : @schedule Job (ideal.processor_state Job))
  {JobReady0 : @JobReady Job (ideal.processor_state Job) Cost Arrival},
@work_bearing_readiness Job Arrival Cost (ideal.processor_state Job) JobReady0 arr_seq sched
  (@FP_to_JLFP Job Task H1 FP) ->
@valid_schedule Job Arrival (ideal.processor_state Job) sched Cost JobReady0 arr_seq ->
@work_conserving.work_conserving Job Arrival Cost (ideal.processor_state Job) JobReady0 arr_seq sched ->
@sequential_tasks Job Task H1 Arrival Cost (ideal.processor_state Job) arr_seq sched ->
@arrivals_have_valid_job_costs Task H Job H1 Cost arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
forall {H3 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H3) ->
@taskset_respects_max_arrivals Task Job H1 arr_seq H3 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@valid_preemption_model Job Cost H2 (ideal.processor_state Job) arr_seq sched ->
@valid_task_run_to_completion_threshold Task H Job H1 Cost H2 H0 arr_seq tsk ->
forall priority_inversion_bound : duration,
@priority_inversion_is_bounded_by Task Job H1 Arrival Cost (ideal.processor_state Job) arr_seq sched
  (@FP_to_JLFP Job Task H1 FP) tsk (@constant duration duration priority_inversion_bound) ->
forall L : duration,
is_true (0 < L) ->
L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H H3 ts FP tsk L ->
forall R : duration,
(forall A : duration,
 is_true (@is_in_search_space Task H H3 tsk L A) ->
 exists F : duration,
   is_true
     (priority_inversion_bound +
      (@task_request_bound_function Task H H3 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H0 tsk)) +
      @total_ohep_request_bound_function_FP Task H H3 ts FP tsk (A + F) <= A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
@task_response_time_bound Task Job Arrival Cost H1 (ideal.processor_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_fp is not universe polymorphic
Arguments uniprocessor_response_time_bound_fp {Task H H0 Job H1 Arrival Cost H2 FP} 
  H_priority_is_reflexive arr_seq H_valid_arrival_sequence sched {JobReady0} H_job_ready 
  H_sched_valid H_work_conserving H_sequential_tasks H_valid_job_cost ts%seq_scope 
  H_all_jobs_from_taskset {H3} H_valid_arrival_curve H_is_arrival_curve tsk H_tsk_in_ts
  H_valid_preemption_model H_valid_run_to_completion_threshold priority_inversion_bound
  H_priority_inversion_is_bounded L H_L_positive H_fixed_point R H_R_is_maximum%function_scope 
  j _ _
uniprocessor_response_time_bound_fp is opaque
Expands to: Constant prosa.results.rta.ideal.fp.bounded_pi.uniprocessor_response_time_bound_fp
Declared in library prosa.results.rta.ideal.fp.bounded_pi, line 324, characters 10-45
@uniprocessor_response_time_bound_fp
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H2 : JobPreemptable Job) (FP : FP_policy Task),
       @reflexive_task_priorities Task FP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (sched : @schedule Job (ideal.processor_state Job))
         (JobReady0 : @JobReady Job (ideal.processor_state Job) Cost Arrival),
       @work_bearing_readiness Job Arrival Cost (ideal.processor_state Job) JobReady0 arr_seq sched
         (@FP_to_JLFP Job Task H1 FP) ->
       @valid_schedule Job Arrival (ideal.processor_state Job) sched Cost JobReady0 arr_seq ->
       @work_conserving.work_conserving Job Arrival Cost (ideal.processor_state Job) JobReady0 arr_seq sched ->
       @sequential_tasks Job Task H1 Arrival Cost (ideal.processor_state Job) arr_seq sched ->
       @arrivals_have_valid_job_costs Task H Job H1 Cost arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       forall H3 : MaxArrivals Task,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H3) ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq H3 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       @valid_preemption_model Job Cost H2 (ideal.processor_state Job) arr_seq sched ->
       @valid_task_run_to_completion_threshold Task H Job H1 Cost H2 H0 arr_seq tsk ->
       forall priority_inversion_bound : duration,
       @priority_inversion_is_bounded_by Task Job H1 Arrival Cost (ideal.processor_state Job) arr_seq sched
         (@FP_to_JLFP Job Task H1 FP) tsk (@constant duration duration priority_inversion_bound) ->
       forall L : duration,
       is_true (0 < L) ->
       L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H H3 ts FP tsk L ->
       forall R : duration,
       (forall A : duration,
        is_true (@is_in_search_space Task H H3 tsk L A) ->
        exists F : duration,
          is_true
            (priority_inversion_bound +
             (@task_request_bound_function Task H H3 tsk (A + 1) -
              (@task_cost Task H tsk - @task_rtct Task H0 tsk)) +
             @total_ohep_request_bound_function_FP Task H H3 ts FP tsk (A + F) <= 
             A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
       @task_response_time_bound Task Job Arrival Cost H1 (ideal.processor_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.BoundedPi.uniprocessor_response_time_bound_fp : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  [FP : Prosa.Model.Priority.Definitions.FP_policy Task],
  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
          [inst_8 : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
          Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                    ∀ (ts : List Task),
                      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                        ∀ [inst_9 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                          Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                              Prosa.Model.Task.Arrival.Curves.max_arrivals →
                            Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                              ∀ (tsk : Task),
                                decide (tsk ∈ ts) = true →
                                  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                                    Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold
                                        arr_seq tsk →
                                      ∀ (priority_inversion_bound : Prosa.Behavior.Time.duration),
                                        Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by
                                            arr_seq sched tsk (Prosa.Util.Notation.constant priority_inversion_bound) →
                                          ∀ (L : Prosa.Behavior.Time.duration),
                                            0 < L →
                                              L =
                                                  priority_inversion_bound +
                                                    Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP
                                                      ts tsk L →
                                                ∀ (R : Prosa.Behavior.Time.duration),
                                                  (∀ (A : Prosa.Behavior.Time.duration),
                                                      Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space tsk L A =
                                                          true →
                                                        ∃ F,
                                                          priority_inversion_bound +
                                                                  (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                                      tsk (A + 1) -
                                                                    (Prosa.Model.Task.Concept.task_cost tsk -
                                                                      Prosa.Model.Task.Preemption.Parameters.task_rtct
                                                                        tsk)) +
                                                                Prosa.Analysis.Definitions.RequestBoundFunction.total_ohep_request_bound_function_FP
                                                                  ts tsk (A + F) ≤
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
Prosa_Results_Rta_Ideal_Fp_BoundedPi_uniprocessor_response_time_bound_fp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
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
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_20 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_7
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_7))
         (inst_50 : 
          Prosa_Behavior_Ready_JobReady_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_23
            inst_20),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness_inst4 Job
         inst_7
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         inst_50 arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_7 Task
            inst_3
            inst_16 FP) ->
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_23
         inst_50 arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_7
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         inst_50 arr_seq sched ->
       Prosa_Model_Task_Sequentiality_sequential_tasks_inst8 Job
         inst_7 Task
         inst_3
         inst_16
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_23 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_16 arr_seq ts ->
       forall
         inst_99 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_99) ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_16 arr_seq
         inst_99 ts ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_7
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_23
         inst_26
         inst_13 arr_seq tsk ->
       forall priority_inversion_bound : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by_inst8 Task
         inst_3 Job
         inst_7
         inst_16
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_7 Task
            inst_3
            inst_16 FP)
         tsk
         (Prosa_Util_Notation_constant_inst3 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            priority_inversion_bound) ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) priority_inversion_bound
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
               inst_3
               inst_10
               inst_99 ts FP tsk L)) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Fp_BoundedPi_is_in_search_space Task
             inst_3
             inst_10
             inst_99 tsk L A)
          Bool_true ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                   (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                      (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) priority_inversion_bound
                      (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                            inst_3
                            inst_10
                            inst_99 tsk
                            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                               Prosa_Behavior_Time_duration
                               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                               (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 ...)))
                         (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                            Prosa_Behavior_Time_duration
                            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                               inst_3
                               inst_10 tsk)
                            (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct
                               Task inst_3
                               inst_13 tsk))))
                   (Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP Task
                      inst_3
                      inst_10
                      inst_99 ts FP tsk
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
                         inst_13 tsk)))
                R))) ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8 Task
         inst_3 Job
         inst_7
         inst_20
         inst_23
         inst_16
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched tsk R
```
