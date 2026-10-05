# `uniprocessor_response_time_bound_fully_nonpreemptive_edf`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.ideal.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf`
- Lean: `Prosa.Results.Rta.Ideal.Edf.FullyNonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf`
- Certificate: `uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fully_nonpreemptive_edf :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H2 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall {H4 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H4) ->
@taskset_respects_max_arrivals Task Job H1 arr_seq H4 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job H2 (ideal.processor_state Job) sched H3
  (@basic_ready_instance Job (ideal.processor_state Job) H2 H3) arr_seq ->
@nonpreemptive_schedule Job H3 (ideal.processor_state Job) sched ->
@work_conserving Job H2 H3 (ideal.processor_state Job)
  (@basic_ready_instance Job (ideal.processor_state Job) H2 H3) arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H2 H3 (ideal.processor_state Job)
  (@fully_nonpreemptive_job_model Job H3) (@basic_ready_instance Job (ideal.processor_state Job) H2 H3)
  arr_seq sched (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H2 H1)) ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H4 ts L ->
forall R : nat,
(forall A : duration,
 is_true (@is_in_search_space Task H H0 ts H4 tsk L A) ->
 exists F : nat,
   is_true
     ((fun A0 : nat =>
       \max_(tsk_o <- ts | @blocking_relevant Task H H4 tsk_o &&
                           (@task_deadline Task H0 tsk + A0 < @task_deadline Task H0 tsk_o))
          (@task_cost Task H tsk_o - 1))
        A +
      (@task_request_bound_function Task H H4 tsk (A + 1) - (@task_cost Task H tsk - 1)) +
      @bound_on_athep_workload Task H H0 H4 ts tsk A (A + F) <= A + F) /\
   is_true (F + (@task_cost Task H tsk - 1) <= R)) ->
@task_response_time_bound Task Job H2 H3 H1 (ideal.processor_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_fully_nonpreemptive_edf is not universe polymorphic
Arguments uniprocessor_response_time_bound_fully_nonpreemptive_edf {Task H H0 Job H1 H2 H3} 
  arr_seq H_valid_arrival_sequence ts%seq_scope H_all_jobs_from_taskset H_valid_job_cost 
  {H4} H_valid_arrival_curve H_is_arrival_curve tsk H_tsk_in_ts sched H_sched_valid 
  H_nonpreemptive_sched H_work_conserving H_respects_policy L H_L_positive H_fixed_point 
  R%nat_scope H_R_is_maximum%function_scope j _ _
uniprocessor_response_time_bound_fully_nonpreemptive_edf is opaque
Expands to: Constant
            prosa.results.rta.ideal.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf
Declared in library prosa.results.rta.ideal.edf.fully_nonpreemptive, line 119, characters 10-66
@uniprocessor_response_time_bound_fully_nonpreemptive_edf
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H2 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall H4 : MaxArrivals Task,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H4) ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq H4 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job H2 (ideal.processor_state Job) sched H3
         (@basic_ready_instance Job (ideal.processor_state Job) H2 H3) arr_seq ->
       @nonpreemptive_schedule Job H3 (ideal.processor_state Job) sched ->
       @work_conserving Job H2 H3 (ideal.processor_state Job)
         (@basic_ready_instance Job (ideal.processor_state Job) H2 H3) arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H2 H3 (ideal.processor_state Job)
         (@fully_nonpreemptive_job_model Job H3)
         (@basic_ready_instance Job (ideal.processor_state Job) H2 H3) arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H2 H1)) ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H4 ts L ->
       forall R : nat,
       (forall A : duration,
        is_true (@is_in_search_space Task H H0 ts H4 tsk L A) ->
        exists F : nat,
          is_true
            (\max_(tsk_o <- ts | @blocking_relevant Task H H4 tsk_o &&
                                 (@task_deadline Task H0 tsk + A < @task_deadline Task H0 tsk_o))
                (@task_cost Task H tsk_o - 1) +
             (@task_request_bound_function Task H H4 tsk (A + 1) - (@task_cost Task H tsk - 1)) +
             @bound_on_athep_workload Task H H0 H4 ts tsk A (A + F) <= A + F) /\
          is_true (F + (@task_cost Task H tsk - 1) <= R)) ->
       @task_response_time_bound Task Job H2 H3 H1 (ideal.processor_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Edf.FullyNonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task] {Job : Prosa.Behavior.Job.JobType} [inst_3 : DecidableEq Job]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : List Task),
      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
        Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
          ∀ [inst_7 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
            Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                Prosa.Model.Task.Arrival.Curves.max_arrivals →
              Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                ∀ (tsk : Task),
                  decide (tsk ∈ ts) = true →
                    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
                      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                        Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule sched →
                          Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                            Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                                (Prosa.Model.Priority.Edf.EDF Job) →
                              ∀ (L : Prosa.Behavior.Time.duration),
                                0 < L →
                                  L =
                                      Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts
                                        L →
                                    ∀ (R : ℕ),
                                      (∀ (A : Prosa.Behavior.Time.duration),
                                          Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space ts tsk L A = true →
                                            ∃ F,
                                              (Prosa.Util.Minmax.bigMaxListCond ts
                                                        (fun tsk_o =>
                                                          Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_relevant
                                                              tsk_o &&
                                                            decide
                                                              (Prosa.Model.Task.Concept.task_deadline tsk + A <
                                                                Prosa.Model.Task.Concept.task_deadline tsk_o))
                                                        fun tsk_o => Prosa.Model.Task.Concept.task_cost tsk_o - 1) +
                                                      (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                          tsk (A + 1) -
                                                        (Prosa.Model.Task.Concept.task_cost tsk - 1)) +
                                                    Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload
                                                      ts tsk A (A + F) ≤
                                                  A + F ∧
                                                F + (Prosa.Model.Task.Concept.task_cost tsk - 1) ≤ R) →
                                        Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched
                                          tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Edf_FullyNonpreemptive_uniprocessor_response_time_bound_fully_nonpreemptive_edf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job)
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_13
         inst_20 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_13
         inst_16 arr_seq ts ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_23 arr_seq ->
       forall
         inst_47 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_47) ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_13
         inst_16 arr_seq
         inst_47 ts ->
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
                   inst_13
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_13),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_13
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_13)
         sched inst_23
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_13
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_13)
            inst_20
            inst_23)
         arr_seq ->
       Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule_inst4 Job
         inst_13
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_13)
         sched ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_13
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_13)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_13
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_13)
            inst_20
            inst_23)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_13
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_13)
         (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
            inst_13
            inst_23)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_13
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_13)
            inst_20
            inst_23)
         arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_13
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_13
               inst_3
               inst_9
               inst_20
               inst_16)) ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_6
            inst_47 ts L) ->
       forall R : Nat,
       (forall A : Prosa_Behavior_Time_duration,
        @eq Bool
          (Prosa_Results_Rta_Ideal_Edf_BoundedNps_is_in_search_space Task
             inst_3
             inst_6
             inst_9 ts
             inst_47 tsk L A)
          Bool_true ->
        Exists Nat
          (fun F : Nat =>
           And
             (LE_le_inst1 Nat instLENat
                (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                   (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
                      (Prosa_Util_Minmax_bigMaxListCond Task ts
                         (fun tsk_o : Task =>
                          Bool_and
                            (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant Task
                               inst_3
                               inst_6
                               inst_47
                               tsk_o)
                            (Decidable_decide
                               (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
                                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                                     Prosa_Behavior_Time_duration
                                     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                                     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                                        inst_3
                                        inst_9
                                        tsk)
                                     A)
                                  (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                                     inst_3
                                     inst_9
                                     tsk_o))
                               (Nat_decLt
                                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                                     Prosa_Behavior_Time_duration
                                     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                                     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                                        inst_3
                                        inst_9
                                        tsk)
                                     A)
                                  (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                                     inst_3
                                     inst_9
                                     tsk_o))))
                         (fun tsk_o : Task =>
                          HSub_hSub_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                               inst_3
                               inst_6
                               tsk_o)
                            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                      (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                            inst_3
                            inst_6
                            inst_47
                            tsk
                            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                               Prosa_Behavior_Time_duration
                               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                               (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                         (HSub_hSub_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                               inst_3
                               inst_6
                               tsk)
                            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))))
                   (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
                      inst_3
                      inst_6
                      inst_9
                      inst_47 ts
                      tsk A
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                   (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
             (LE_le_inst1 Nat instLENat
                (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) F
                   (HSub_hSub_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
                      (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                      (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                         inst_3
                         inst_6
                         tsk)
                      (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                R))) ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8 Task
         inst_3 Job
         inst_13
         inst_20
         inst_23
         inst_16
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_13)
         arr_seq sched tsk R
```
