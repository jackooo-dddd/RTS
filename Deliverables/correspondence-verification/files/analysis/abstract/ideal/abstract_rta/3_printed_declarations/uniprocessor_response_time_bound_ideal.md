# `uniprocessor_response_time_bound_ideal`

- Kind (Rocq): Theorem
- Rocq: `prosa.analysis.abstract.ideal.abstract_rta.uniprocessor_response_time_bound_ideal`
- Lean: `Prosa.Analysis.Abstract.Ideal.AbstractRta.uniprocessor_response_time_bound_ideal`
- Certificate: `uniprocessor_response_time_bound_ideal_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_ideal :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} 
  {H4 : JobPreemptable Job} {PState : ProcessorState Job},
@ideal_progress_proc_model Job PState ->
@unit_service_proc_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@jobs_must_arrive_to_execute Job H2 PState sched ->
@completed_jobs_dont_execute Job PState sched H3 ->
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_preemption_model Job H3 H4 PState arr_seq sched ->
@valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
forall {H5 : Interference Job} {H6 : InterferingWorkload Job},
@work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
forall L : duration,
@busy_intervals_are_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6 L ->
forall interference_bound_function : duration -> duration -> duration,
@job_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6 interference_bound_function
  (@relative_arrival_time_of_job_is_A Job H2 H3 PState sched H5 H6) ->
forall R : duration,
(forall A : nat,
 [eta is_in_search_space L interference_bound_function] A ->
 exists F : nat,
   is_true (@task_rtct Task H0 tsk + interference_bound_function A (A + F) <= A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
@task_response_time_bound Task Job H2 H3 H1 PState arr_seq sched tsk R

uniprocessor_response_time_bound_ideal is not universe polymorphic
Arguments uniprocessor_response_time_bound_ideal {Task H H0 Job H1 H2 H3 H4 PState}
  H_ideal_progress_proc_model H_unit_service_proc_model arr_seq sched H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_valid_job_cost ts%seq_scope tsk H_tsk_in_ts H_valid_preemption_model
  H_valid_run_to_completion_threshold {H5 H6} H_work_conserving L H_busy_interval_exists
  interference_bound_function%function_scope H_job_interference_is_bounded R
  H_R_is_maximum_ideal%function_scope j _ _
uniprocessor_response_time_bound_ideal is opaque
Expands to: Constant prosa.analysis.abstract.ideal.abstract_rta.uniprocessor_response_time_bound_ideal
Declared in library prosa.analysis.abstract.ideal.abstract_rta, line 179, characters 10-48
@uniprocessor_response_time_bound_ideal
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job)
         (H4 : JobPreemptable Job) (PState : ProcessorState Job),
       @ideal_progress_proc_model Job PState ->
       @unit_service_proc_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @jobs_must_arrive_to_execute Job H2 PState sched ->
       @completed_jobs_dont_execute Job PState sched H3 ->
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_preemption_model Job H3 H4 PState arr_seq sched ->
       @valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
       forall (H5 : Interference Job) (H6 : InterferingWorkload Job),
       @work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
       forall L : duration,
       @busy_intervals_are_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6 L ->
       forall interference_bound_function : duration -> duration -> duration,
       @job_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6
         interference_bound_function (@relative_arrival_time_of_job_is_A Job H2 H3 PState sched H5 H6) ->
       forall R : duration,
       (forall A : nat,
        is_in_search_space L interference_bound_function A ->
        exists F : nat,
          is_true (@task_rtct Task H0 tsk + interference_bound_function A (A + F) <= A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
       @task_response_time_bound Task Job H2 H3 H1 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.AbstractRta.uniprocessor_response_time_bound_ideal : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
        (sched : Prosa.Behavior.Schedule.schedule PState),
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
            Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
              ∀ (ts : List Task) (tsk : Task),
                decide (tsk ∈ ts) = true →
                  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                    Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
                      ∀ [inst_8 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                        [inst_9 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                        Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                          ∀ (L : Prosa.Behavior.Time.duration),
                            Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by arr_seq sched tsk L →
                              ∀
                                (interference_bound_function :
                                  Prosa.Behavior.Time.duration →
                                    Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                                Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched tsk
                                    interference_bound_function
                                    (Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A sched) →
                                  ∀ (R : Prosa.Behavior.Time.duration),
                                    (∀ (A : ℕ),
                                        Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                                            interference_bound_function A →
                                          ∃ F,
                                            Prosa.Model.Task.Preemption.Parameters.task_rtct tsk +
                                                  interference_bound_function A (A + F) ≤
                                                A + F ∧
                                              F +
                                                  (Prosa.Model.Task.Concept.task_cost tsk -
                                                    Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                                                R) →
                                      Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched
                                        tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_AbstractRta_uniprocessor_response_time_bound_ideal
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_13)
         (inst_26 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_13)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_13),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_13 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_13 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_13 PState),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_13
         inst_20 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_13 PState sched
         inst_23 ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_13
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
         inst_13
         inst_23
         inst_26 PState arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_23
         inst_26
         inst_9 arr_seq tsk ->
       forall
         (inst_81 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_13)
         (inst_84 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_13),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_13
         inst_81
         inst_84
         inst_20
         inst_23 PState arr_seq sched ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_busy_intervals_are_bounded_by Job
         inst_13
         inst_81
         inst_84
         inst_20
         inst_23 PState arr_seq sched
         Task inst_3
         inst_16 tsk L ->
       forall
         interference_bound_function : Prosa_Behavior_Time_duration ->
                                       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job
         inst_13
         inst_81
         inst_84
         inst_20
         inst_23 PState arr_seq sched
         Task inst_3
         inst_16 tsk
         interference_bound_function
         (Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A Job
            inst_13
            inst_20
            inst_23 PState sched
            inst_81
            inst_84) ->
       forall R : Prosa_Behavior_Time_duration,
       (forall A : Nat,
        Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L interference_bound_function A ->
        Exists Nat
          (fun F : Nat =>
           And
             (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                   (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                   (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                      inst_3
                      inst_9 tsk)
                   (interference_bound_function A
                      (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A F)))
                (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) A F))
             (LE_le_inst1 Nat instLENat
                (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) F
                   (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                      Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                      (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                         inst_3
                         inst_6 tsk)
                      (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                         inst_3
                         inst_9 tsk)))
                R))) ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_13
         inst_20
         inst_23
         inst_16 PState arr_seq sched
         tsk R
```
