# `uniprocessor_response_time_bound_FIFO`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.ideal.fifo.bounded_nps.uniprocessor_response_time_bound_FIFO`
- Lean: `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.uniprocessor_response_time_bound_FIFO`
- Certificate: `uniprocessor_response_time_bound_FIFO_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_FIFO :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {H1 : TaskRunToCompletionThreshold Task}
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobArrival Job} {H4 : JobCost Job} 
  {H5 : JobPreemptable Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
@arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@valid_task_run_to_completion_threshold Task H Job H2 H4 H5 H1 arr_seq tsk ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job H3 (ideal.processor_state Job) sched H4
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
@valid_preemption_model Job H4 H5 (ideal.processor_state Job) arr_seq sched ->
@priority_driven.respects_JLFP_policy_at_preemption_point Job H3 H4 (ideal.processor_state Job) H5
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched 
  (@fifo.FIFO Job H3) ->
@work_conserving.work_conserving Job H3 H4 (ideal.processor_state Job)
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H0 ts L ->
forall R : duration,
(forall A : duration,
 is_true (@is_in_concrete_search_space Task H H0 ts L A) ->
 exists F : nat,
   is_true (\sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A + 1) <= A + F) /\
   is_true (F <= R)) ->
@task_response_time_bound Task Job H3 H4 H2 (ideal.processor_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_FIFO is not universe polymorphic
Arguments uniprocessor_response_time_bound_FIFO {Task H H0 H1 Job H2 H3 H4 H5} arr_seq
  H_valid_arrival_sequence H_valid_job_cost ts%seq_scope H_all_jobs_from_taskset 
  H_is_arrival_curve H_valid_arrival_curve tsk H_tsk_in_ts H_valid_run_to_completion_threshold 
  sched H_valid_schedule H_valid_preemption_model H_respects_policy_at_preemption_point 
  H_work_conserving L H_L_positive H_fixed_point R H_R_max%function_scope j _ _
uniprocessor_response_time_bound_FIFO is opaque
Expands to: Constant prosa.results.rta.ideal.fifo.bounded_nps.uniprocessor_response_time_bound_FIFO
Declared in library prosa.results.rta.ideal.fifo.bounded_nps, line 448, characters 10-47
@uniprocessor_response_time_bound_FIFO
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task)
         (H1 : TaskRunToCompletionThreshold Task) (Job : JobType) (H2 : JobTask Job Task)
         (H3 : JobArrival Job) (H4 : JobCost Job) (H5 : JobPreemptable Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       @valid_task_run_to_completion_threshold Task H Job H2 H4 H5 H1 arr_seq tsk ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job H3 (ideal.processor_state Job) sched H4
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
       @valid_preemption_model Job H4 H5 (ideal.processor_state Job) arr_seq sched ->
       @priority_driven.respects_JLFP_policy_at_preemption_point Job H3 H4 (ideal.processor_state Job) H5
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched
         (@fifo.FIFO Job H3) ->
       @work_conserving.work_conserving Job H3 H4 (ideal.processor_state Job)
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H0 ts L ->
       forall R : duration,
       (forall A : duration,
        is_true (@is_in_concrete_search_space Task H H0 ts L A) ->
        exists F : nat,
          is_true (\sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A + 1) <= A + F) /\
          is_true (F <= R)) ->
       @task_response_time_bound Task Job H3 H4 H2 (ideal.processor_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fifo.BoundedNps.uniprocessor_response_time_bound_FIFO : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_4 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_6 : Prosa.Behavior.Job.JobArrival Job]
  [inst_7 : Prosa.Behavior.Job.JobCost Job] [inst_8 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (ts : List Task),
        Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
            Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                Prosa.Model.Task.Arrival.Curves.max_arrivals →
              ∀ (tsk : Task),
                decide (tsk ∈ ts) = true →
                  Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
                    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
                      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                        Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                          Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                              (Prosa.Model.Priority.Fifo.FIFO Job) →
                            Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                              ∀ (L : Prosa.Behavior.Time.duration),
                                0 < L →
                                  L =
                                      Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts
                                        L →
                                    ∀ (R : Prosa.Behavior.Time.duration),
                                      (∀ (A : Prosa.Behavior.Time.duration),
                                          Prosa.Results.Rta.Ideal.Fifo.BoundedNps.is_in_concrete_search_space ts L A =
                                              true →
                                            ∃ F,
                                              (Prosa.Util.Sum.sumSeq ts fun tsko =>
                                                    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                      tsko (A + 1)) ≤
                                                  A + F ∧
                                                F ≤ R) →
                                        Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched
                                          tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fifo_BoundedNps_uniprocessor_response_time_bound_FIFO
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_23 arr_seq ->
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
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_19 arr_seq
         inst_13 ts ->
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_13) ->
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
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_19
         inst_26
         inst_29
         inst_16 arr_seq tsk ->
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
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_7
         inst_26
         inst_29
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
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
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_7
            inst_23) ->
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
            inst_13 ts L) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Fifo_BoundedNps_is_in_concrete_search_space Task
             inst_3
             inst_10
             inst_13 ts L A)
          Bool_true ->
        Exists Nat
          (fun F : Nat =>
           And
             (LE_le_inst1 Nat instLENat
                (Prosa_Util_Sum_sumSeq Task ts
                   (fun tsko : Task =>
                    Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                      inst_3
                      inst_10
                      inst_13 tsko
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                         Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                   (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
             (LE_le_inst1 Nat instLENat F R))) ->
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
