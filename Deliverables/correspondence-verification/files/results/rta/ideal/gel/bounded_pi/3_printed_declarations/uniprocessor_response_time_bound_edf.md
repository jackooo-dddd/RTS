# `uniprocessor_response_time_bound_edf`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.ideal.gel.bounded_pi.uniprocessor_response_time_bound_edf`
- Lean: `Prosa.Results.Rta.Ideal.Gel.BoundedPi.uniprocessor_response_time_bound_edf`
- Certificate: `uniprocessor_response_time_bound_edf_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_edf :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {H2 : MaxArrivals Task} {Job : JobType} {H3 : JobTask Job Task} {Arrival : JobArrival Job}
  {Cost : JobCost Job} {H4 : JobPreemptable Job} {H5 : gel.PriorityPoint Task}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
  (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
@priority_driven.respects_JLFP_policy_at_preemption_point Job Arrival Cost (ideal.processor_state Job) H4
  (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched
  (@gel.GEL Job Task H5 Arrival H3) ->
@arrivals_have_valid_job_costs Task H Job H3 Cost arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H3 arr_seq ts ->
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H2) ->
@taskset_respects_max_arrivals Task Job H3 arr_seq H2 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@valid_preemption_model Job Cost H4 (ideal.processor_state Job) arr_seq sched ->
@valid_task_run_to_completion_threshold Task H Job H3 Cost H4 H0 arr_seq tsk ->
forall priority_inversion_bound : duration -> duration,
@priority_inversion.priority_inversion_is_bounded_by Task Job H3 Arrival Cost (ideal.processor_state Job)
  arr_seq sched (@gel.GEL Job Task H5 Arrival H3) tsk priority_inversion_bound ->
@work_conserving.work_conserving Job Arrival Cost (ideal.processor_state Job)
  (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H2 ts L ->
forall R : duration,
(forall A : duration,
 is_true (@is_in_search_space Task H H2 H5 ts tsk priority_inversion_bound L A) ->
 exists F : duration,
   is_true
     (priority_inversion_bound A +
      (@task_request_bound_function Task H H2 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H0 tsk)) +
      (fun A0 Δ : duration =>
       \sum_(tsk_o <- ts | tsk_o != tsk)
          @task_request_bound_function Task H H2 tsk_o
            (minn
               (ssrint.absz
                  (@order.Order.max ssrnum.ring_display
                     (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                        ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                     (@ssralg.GRing.zero (...)) ((...) tsk_o A0)))
               Δ))
        A (A + F) <=
      A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
@task_response_time_bound Task Job Arrival Cost H3 (ideal.processor_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_edf is not universe polymorphic
Arguments uniprocessor_response_time_bound_edf {Task H H0 H2 Job H3 Arrival Cost H4 H5} 
  arr_seq H_valid_arrival_sequence sched H_sched_valid H_respects_policy H_valid_job_cost 
  ts%seq_scope H_all_jobs_from_taskset H_valid_arrival_curve H_is_arrival_curve tsk 
  H_tsk_in_ts H_valid_preemption_model H_valid_run_to_completion_threshold
  priority_inversion_bound%function_scope H_priority_inversion_is_bounded H_work_conserving 
  L H_L_positive H_fixed_point R H_R_is_maximum%function_scope j _ _
uniprocessor_response_time_bound_edf is opaque
Expands to: Constant prosa.results.rta.ideal.gel.bounded_pi.uniprocessor_response_time_bound_edf
Declared in library prosa.results.rta.ideal.gel.bounded_pi, line 382, characters 10-46
@uniprocessor_response_time_bound_edf
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task)
         (H2 : MaxArrivals Task) (Job : JobType) (H3 : JobTask Job Task) (Arrival : JobArrival Job)
         (Cost : JobCost Job) (H4 : JobPreemptable Job) (H5 : gel.PriorityPoint Task)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
         (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
       @priority_driven.respects_JLFP_policy_at_preemption_point Job Arrival Cost 
         (ideal.processor_state Job) H4
         (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched
         (@gel.GEL Job Task H5 Arrival H3) ->
       @arrivals_have_valid_job_costs Task H Job H3 Cost arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H3 arr_seq ts ->
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H2) ->
       @taskset_respects_max_arrivals Task Job H3 arr_seq H2 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       @valid_preemption_model Job Cost H4 (ideal.processor_state Job) arr_seq sched ->
       @valid_task_run_to_completion_threshold Task H Job H3 Cost H4 H0 arr_seq tsk ->
       forall priority_inversion_bound : duration -> duration,
       @priority_inversion.priority_inversion_is_bounded_by Task Job H3 Arrival Cost
         (ideal.processor_state Job) arr_seq sched (@gel.GEL Job Task H5 Arrival H3) tsk
         priority_inversion_bound ->
       @work_conserving.work_conserving Job Arrival Cost (ideal.processor_state Job)
         (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq sched ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H2 ts L ->
       forall R : duration,
       (forall A : duration,
        is_true (@is_in_search_space Task H H2 H5 ts tsk priority_inversion_bound L A) ->
        exists F : duration,
          is_true
            (priority_inversion_bound A +
             (@task_request_bound_function Task H H2 tsk (A + 1) -
              (@task_cost Task H tsk - @task_rtct Task H0 tsk)) +
             \sum_(tsk_o <- ts | tsk_o != tsk)
                @task_request_bound_function Task H H2 tsk_o
                  (minn
                     (ssrint.absz
                        (@order.Order.max ssrnum.ring_display
                           (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                              ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                           (@ssralg.GRing.zero
                              (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                                 ssrint.ssrint_int__canonical__Num_POrderedZmodule))
                           (@ssralg.GRing.add
                              (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                 ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                              (@ssralg.GRing.add
                                 (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                    ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                                 (@ssralg.GRing.natmul
                                    (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                       ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                                    (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) 
                                    (A + 1))
                                 (@gel.task_priority_point Task H5 tsk))
                              (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                                 (@gel.task_priority_point Task H5 tsk_o)))))
                     (A + F)) <=
             A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
       @task_response_time_bound Task Job Arrival Cost H3 (ideal.processor_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Gel.BoundedPi.uniprocessor_response_time_bound_edf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobArrival Job] [inst_7 : Prosa.Behavior.Job.JobCost Job]
  [inst_8 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] [inst_9 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
            (Prosa.Model.Priority.Gel.GEL Job Task) →
          Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
            ∀ (ts : List Task),
              Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                    Prosa.Model.Task.Arrival.Curves.max_arrivals →
                  Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                    ∀ (tsk : Task),
                      decide (tsk ∈ ts) = true →
                        Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                          Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
                            ∀ (priority_inversion_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                              Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by arr_seq
                                  sched tsk priority_inversion_bound →
                                Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                                  ∀ (L : Prosa.Behavior.Time.duration),
                                    0 < L →
                                      L =
                                          Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function
                                            ts L →
                                        ∀ (R : Prosa.Behavior.Time.duration),
                                          (∀ (A : Prosa.Behavior.Time.duration),
                                              Prosa.Results.Rta.Ideal.Gel.BoundedPi.is_in_search_space ts tsk
                                                    priority_inversion_bound L A =
                                                  true →
                                                ∃ F,
                                                  (priority_inversion_bound A +
                                                          (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                              tsk (A + 1) -
                                                            (Prosa.Model.Task.Concept.task_cost tsk -
                                                              Prosa.Model.Task.Preemption.Parameters.task_rtct tsk)) +
                                                        Prosa.Util.Sum.sumFiltered ts
                                                          (fun tsk_o => decide (tsk_o ≠ tsk)) fun tsk_o =>
                                                          Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                            tsk_o
                                                            (min
                                                              (max 0
                                                                  (↑(A + 1) +
                                                                      Prosa.Model.Priority.Gel.task_priority_point tsk -
                                                                    Prosa.Model.Priority.Gel.task_priority_point
                                                                      tsk_o)).natAbs
                                                              (A + F))) ≤
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
Prosa_Results_Rta_Ideal_Gel_BoundedPi_uniprocessor_response_time_bound_edf
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
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_19 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_23 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_26 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_29 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (inst_32 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_23 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_26
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_23
            inst_26)
         arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_7
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         inst_29
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_23
            inst_26)
         arr_seq sched
         (Prosa_Model_Priority_Gel_GEL Job
            inst_7 Task
            inst_3
            inst_32
            inst_23
            inst_19) ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_19
         inst_26 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_19 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_16) ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_19 arr_seq
         inst_16 ts ->
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
         inst_26
         inst_29
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_19
         inst_26
         inst_29
         inst_13 arr_seq tsk ->
       forall priority_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by_inst8 Task
         inst_3 Job
         inst_7
         inst_19
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
         (Prosa_Model_Priority_Gel_GEL Job
            inst_7 Task
            inst_3
            inst_32
            inst_23
            inst_19)
         tsk priority_inversion_bound ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_7
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_23
            inst_26)
         arr_seq sched ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_10
            inst_16 ts L) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Gel_BoundedPi_is_in_search_space Task
             inst_3
             inst_10
             inst_16
             inst_32 ts tsk
             priority_inversion_bound L A)
          Bool_true ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                   (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                      (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (priority_inversion_bound A)
                      (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                            inst_3
                            inst_10
                            inst_16 tsk
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
                               inst_13
                               tsk))))
                   (Prosa_Util_Sum_sumFiltered Task ts
                      (fun tsk_o : Task =>
                       Decidable_decide (Ne Task tsk_o tsk)
                         (instDecidableNot (@eq Task tsk_o tsk)
                            (inst_3 tsk_o
                               tsk)))
                      (fun tsk_o : Task =>
                       Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                         inst_3
                         inst_10
                         inst_16 tsk_o
                         (Min_min_inst1 Prosa_Behavior_Time_duration instMinNat
                            (Int_natAbs
                               (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (...))
                                  (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (...) (...) (...))))
                            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                               Prosa_Behavior_Time_duration
                               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))))
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
         inst_23
         inst_26
         inst_19
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched tsk R
```
