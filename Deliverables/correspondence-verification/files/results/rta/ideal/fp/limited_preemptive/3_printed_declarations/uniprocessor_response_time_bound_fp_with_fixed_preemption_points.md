# `uniprocessor_response_time_bound_fp_with_fixed_preemption_points`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.ideal.fp.limited_preemptive.uniprocessor_response_time_bound_fp_with_fixed_preemption_points`
- Lean: `Prosa.Results.Rta.Ideal.Fp.LimitedPreemptive.uniprocessor_response_time_bound_fp_with_fixed_preemption_points`
- Certificate: `uniprocessor_response_time_bound_fp_with_fixed_preemption_points_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fp_with_fixed_preemption_points :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H0 arr_seq ts ->
@arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
forall {H3 : JobPreemptionPoints Job} {H4 : TaskPreemptionPoints Task},
@valid_fixed_preemption_points_model Task H H4 Job H0 H2 H3 arr_seq ts ->
forall {H5 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
@taskset_respects_max_arrivals Task Job H0 arr_seq H5 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job H1 (ideal.processor_state Job) sched H2 (@sequential_readiness Task Job H0 H1 H2 arr_seq)
  arr_seq ->
@schedule_respects_preemption_model Job (ideal.processor_state Job) (@limited_preemptive_job_model Job H3)
  arr_seq sched ->
forall {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
@work_conserving Job H1 H2 (ideal.processor_state Job) (@sequential_readiness Task Job H0 H1 H2 arr_seq)
  arr_seq sched ->
@respects_FP_policy_at_preemption_point Task Job H0 H1 H2 (ideal.processor_state Job)
  (@limited_preemptive_job_model Job H3) (@sequential_readiness Task Job H0 H1 H2 arr_seq) arr_seq sched FP ->
forall L : duration,
is_true (0 < L) ->
L =
@blocking_bound Task (@TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task H4) FP ts tsk +
@total_hep_request_bound_function_FP Task H H5 ts FP tsk L ->
forall R : nat,
(forall A : duration,
 is_true (@is_in_search_space Task H H5 tsk L A) ->
 exists F : duration,
   is_true
     (@blocking_bound Task (@TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task H4) FP ts
        tsk +
      (@task_request_bound_function Task H H5 tsk (A + 1) - (@task_last_nonpr_segment Task H4 tsk - 1)) +
      @total_ohep_request_bound_function_FP Task H H5 ts FP tsk (A + F) <= A + F) /\
   is_true (F + (@task_last_nonpr_segment Task H4 tsk - 1) <= R)) ->
@task_response_time_bound Task Job H1 H2 H0 (ideal.processor_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_fp_with_fixed_preemption_points is not universe polymorphic
Arguments uniprocessor_response_time_bound_fp_with_fixed_preemption_points {Task H Job H0 H1 H2} 
  arr_seq H_valid_arrival_sequence ts%seq_scope H_all_jobs_from_taskset H_valid_job_cost 
  {H3 H4} H_valid_model_with_fixed_preemption_points {H5} H_valid_arrival_curve H_is_arrival_curve 
  tsk H_tsk_in_ts sched H_sched_valid H_schedule_respects_preemption_model {FP} H_priority_is_reflexive
  H_priority_is_transitive H_work_conserving H_respects_policy L H_L_positive H_fixed_point 
  R%nat_scope H_R_is_maximum%function_scope j _ _
uniprocessor_response_time_bound_fp_with_fixed_preemption_points is opaque
Expands to: Constant
            prosa.results.rta.ideal.fp.limited_preemptive.uniprocessor_response_time_bound_fp_with_fixed_preemption_points
Declared in library prosa.results.rta.ideal.fp.limited_preemptive, line 133, characters 10-74
@uniprocessor_response_time_bound_fp_with_fixed_preemption_points
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H0 arr_seq ts ->
       @arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
       forall (H3 : JobPreemptionPoints Job) (H4 : TaskPreemptionPoints Task),
       @valid_fixed_preemption_points_model Task H H4 Job H0 H2 H3 arr_seq ts ->
       forall H5 : MaxArrivals Task,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
       @taskset_respects_max_arrivals Task Job H0 arr_seq H5 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job H1 (ideal.processor_state Job) sched H2
         (@sequential_readiness Task Job H0 H1 H2 arr_seq) arr_seq ->
       @schedule_respects_preemption_model Job (ideal.processor_state Job)
         (@limited_preemptive_job_model Job H3) arr_seq sched ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       @work_conserving Job H1 H2 (ideal.processor_state Job)
         (@sequential_readiness Task Job H0 H1 H2 arr_seq) arr_seq sched ->
       @respects_FP_policy_at_preemption_point Task Job H0 H1 H2 (ideal.processor_state Job)
         (@limited_preemptive_job_model Job H3) (@sequential_readiness Task Job H0 H1 H2 arr_seq) arr_seq
         sched FP ->
       forall L : duration,
       is_true (0 < L) ->
       L =
       @blocking_bound Task (@TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task H4) FP ts
         tsk +
       @total_hep_request_bound_function_FP Task H H5 ts FP tsk L ->
       forall R : nat,
       (forall A : duration,
        is_true (@is_in_search_space Task H H5 tsk L A) ->
        exists F : duration,
          is_true
            (@blocking_bound Task (@TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task H4)
               FP ts tsk +
             (@task_request_bound_function Task H H5 tsk (A + 1) - (@task_last_nonpr_segment Task H4 tsk - 1)) +
             @total_ohep_request_bound_function_FP Task H H5 ts FP tsk (A + F) <= 
             A + F) /\
          is_true (F + (@task_last_nonpr_segment Task H4 tsk - 1) <= R)) ->
       @task_response_time_bound Task Job H1 H2 H0 (ideal.processor_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.LimitedPreemptive.uniprocessor_response_time_bound_fp_with_fixed_preemption_points : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : List Task),
      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
        Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
          ∀ [inst_6 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
            [inst_7 : Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task],
            Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_model arr_seq ts →
              ∀ [inst_8 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                    Prosa.Model.Task.Arrival.Curves.max_arrivals →
                  Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                    ∀ (tsk : Task),
                      decide (tsk ∈ ts) = true →
                        ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
                          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                            Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq sched →
                              ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
                                Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
                                  Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
                                    Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                                      Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq
                                          sched FP →
                                        ∀ (L : Prosa.Behavior.Time.duration),
                                          0 < L →
                                            L =
                                                Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts tsk +
                                                  Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP
                                                    ts tsk L →
                                              ∀ (R : ℕ),
                                                (∀ (A : Prosa.Behavior.Time.duration),
                                                    Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space tsk L A =
                                                        true →
                                                      ∃ F,
                                                        Prosa.Analysis.Definitions.BlockingBound.Fp.blocking_bound ts
                                                                  tsk +
                                                                (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                                    tsk (A + 1) -
                                                                  (Prosa.Model.Task.Preemption.Parameters.task_last_nonpr_segment
                                                                      tsk -
                                                                    1)) +
                                                              Prosa.Analysis.Definitions.RequestBoundFunction.total_ohep_request_bound_function_FP
                                                                ts tsk (A + F) ≤
                                                            A + F ∧
                                                          F +
                                                              (Prosa.Model.Task.Preemption.Parameters.task_last_nonpr_segment
                                                                  tsk -
                                                                1) ≤
                                                            R) →
                                                  Prosa.Analysis.Definitions.Schedulability.task_response_time_bound
                                                    arr_seq sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fp_LimitedPreemptive_uniprocessor_response_time_bound_fp_with_fixed_preemption_points
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_10
         inst_13 arr_seq ts ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_20 arr_seq ->
       forall
         (inst_44 : 
          Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
            inst_10)
         (inst_47 : 
          Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
            inst_3),
       Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_model Task
         inst_3
         inst_6
         inst_47 Job
         inst_10
         inst_13
         inst_20
         inst_44 arr_seq ts ->
       forall
         inst_56 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_56) ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq
         inst_56 ts ->
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
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_10
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_10),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_10
         inst_17
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_10)
         sched inst_20
         (Prosa_Model_Readiness_Sequential_sequential_ready_instance_inst8 Job
            inst_10 Task
            inst_3
            inst_13
            inst_17
            inst_20
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_10)
            arr_seq)
         arr_seq ->
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model_inst4 Job
         inst_10
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_10)
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_10
            inst_44)
         arr_seq sched ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_10
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_10)
         (Prosa_Model_Readiness_Sequential_sequential_ready_instance_inst8 Job
            inst_10 Task
            inst_3
            inst_13
            inst_17
            inst_20
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_10)
            arr_seq)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point_inst8 Task
         inst_3 Job
         inst_10
         inst_13
         inst_17
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_10)
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_10
            inst_44)
         (Prosa_Model_Readiness_Sequential_sequential_ready_instance_inst8 Job
            inst_10 Task
            inst_3
            inst_13
            inst_17
            inst_20
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_10)
            arr_seq)
         arr_seq sched FP ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
               inst_3
               (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
                  Task inst_3
                  inst_47)
               FP ts tsk)
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
               inst_3
               inst_6
               inst_56 ts FP tsk L)) ->
       forall R : Nat,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Fp_BoundedPi_is_in_search_space Task
             inst_3
             inst_6
             inst_56 tsk L A)
          Bool_true ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Nat instLENat
                (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                   (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                      (Prosa_Analysis_Definitions_BlockingBound_Fp_blocking_bound Task
                         inst_3
                         (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
                            Task
                            inst_3
                            inst_47)
                         FP ts tsk)
                      (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
                         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                            inst_3
                            inst_6
                            inst_56
                            tsk
                            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                               Prosa_Behavior_Time_duration
                               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                               (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (...))))
                         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
                            (Prosa_Model_Task_Preemption_Parameters_task_last_nonpr_segment Task
                               inst_3
                               inst_47
                               tsk)
                            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))))
                   (Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP Task
                      inst_3
                      inst_6
                      inst_56 ts
                      FP tsk
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                         Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                   (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) F
                   (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                      (Prosa_Model_Task_Preemption_Parameters_task_last_nonpr_segment Task
                         inst_3
                         inst_47
                         tsk)
                      (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                R))) ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8 Task
         inst_3 Job
         inst_10
         inst_17
         inst_20
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_10)
         arr_seq sched tsk R
```
