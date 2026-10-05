# `uniprocessor_response_time_bound_fully_preemptive_edf`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.rs.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf`
- Lean: `Prosa.Results.Rta.Rs.Edf.FullyPreemptive.uniprocessor_response_time_bound_fully_preemptive_edf`
- Certificate: `uniprocessor_response_time_bound_fully_preemptive_edf_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fully_preemptive_edf :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {H1 : MaxArrivals Task} 
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobArrival Job}
  {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H4 arr_seq ->
@arrivals_have_valid_job_costs Task H Job H2 H3 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H2 arr_seq H1 ts ->
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H1) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall sched : @schedule Job PState,
@valid_schedule Job H4 PState sched H3 (@basic.basic_ready_instance Job PState H4 H3) arr_seq ->
@work_conserving Job H4 H3 PState (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H4 H3 PState (@fully_preemptive_job_model Job)
  (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H4 H2)) ->
forall {SBF : SupplyBoundFunction},
sbf_is_monotone SBF ->
unit_supply_bound_function SBF ->
@valid_busy_sbf Task Job H4 H3 H2 PState arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H4 H2)) tsk SBF ->
forall L : duration,
@busy_window_recurrence_solution Task H H1 ts SBF L ->
forall R : duration,
@rta_recurrence_solution Task H H0 H1 ts tsk SBF L R ->
@task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R

uniprocessor_response_time_bound_fully_preemptive_edf is not universe polymorphic
Arguments uniprocessor_response_time_bound_fully_preemptive_edf {Task H H0 H1 Job H2 H3 H4 PState}
  H_uniprocessor_proc_model H_unit_supply_proc_model H_consumed_supply_proc_model 
  arr_seq H_valid_arrival_sequence H_valid_job_cost ts%seq_scope H_all_jobs_from_taskset 
  H_is_arrival_curve H_valid_arrival_curve tsk H_tsk_in_ts sched H_valid_schedule 
  H_work_conserving H_respects_policy {SBF} H_SBF_monotone H_unit_SBF H_valid_SBF 
  L _ R _ j _ _
uniprocessor_response_time_bound_fully_preemptive_edf is opaque
Expands to: Constant
            prosa.results.rta.rs.edf.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_edf
Declared in library prosa.results.rta.rs.edf.fully_preemptive, line 173, characters 10-63
@uniprocessor_response_time_bound_fully_preemptive_edf
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
         (Job : JobType) (H2 : JobTask Job Task) (H3 : JobCost Job) (H4 : JobArrival Job)
         (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H4 arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H2 H3 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H2 arr_seq H1 ts ->
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H1) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H4 PState sched H3 (@basic.basic_ready_instance Job PState H4 H3) arr_seq ->
       @work_conserving Job H4 H3 PState (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H4 H3 PState (@fully_preemptive_job_model Job)
         (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H4 H2)) ->
       forall SBF : SupplyBoundFunction,
       sbf_is_monotone SBF ->
       unit_supply_bound_function SBF ->
       @valid_busy_sbf Task Job H4 H3 H2 PState arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H4 H2)) tsk SBF ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H1 ts SBF L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 H1 ts tsk SBF L R ->
       @task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Rs.Edf.FullyPreemptive.uniprocessor_response_time_bound_fully_preemptive_edf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_4 : DecidableEq Job] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
          Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
            Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
              ∀ (ts : List Task),
                Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                  Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                    Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                        Prosa.Model.Task.Arrival.Curves.max_arrivals →
                      ∀ (tsk : Task),
                        decide (tsk ∈ ts) = true →
                          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                                Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq
                                    sched (Prosa.Model.Priority.Edf.EDF Job) →
                                  ∀ (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
                                    Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone
                                        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                      Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
                                          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                        Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf arr_seq sched tsk
                                            Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                          ∀ (L : Prosa.Behavior.Time.duration),
                                            Prosa.Results.Rta.Rs.Edf.FullyPreemptive.busy_window_recurrence_solution ts
                                                SBF L →
                                              ∀ (R : Prosa.Behavior.Time.duration),
                                                Prosa.Results.Rta.Rs.Edf.FullyPreemptive.rta_recurrence_solution ts tsk
                                                    SBF L R →
                                                  Prosa.Analysis.Definitions.Schedulability.task_response_time_bound
                                                    arr_seq sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Rs_Edf_FullyPreemptive_uniprocessor_response_time_bound_fully_preemptive_edf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3)
         (inst_12 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : DecidableEq Job)
         (inst_19 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_16 Task
            inst_3)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_16)
         (inst_26 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_16)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_16),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_16 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_16 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_16 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_16,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_16
         inst_26 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_16
         inst_19
         inst_23 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_16
         inst_19 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_16
         inst_19 arr_seq
         inst_12 ts ->
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_12) ->
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
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_16 PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_16
         inst_26 PState sched
         inst_23
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_16 PState
            inst_26
            inst_23)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_16
         inst_26
         inst_23 PState
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_16 PState
            inst_26
            inst_23)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_16
         inst_26
         inst_23 PState
         (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job
            inst_16)
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_16 PState
            inst_26
            inst_23)
         arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_16
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_16
               inst_3
               inst_9
               inst_26
               inst_19)) ->
       forall SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction,
       Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf Task
         inst_3 Job
         inst_16
         inst_26
         inst_23
         inst_19 PState arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_16
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_16
               inst_3
               inst_9
               inst_26
               inst_19))
         tsk (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Rs_Edf_FullyPreemptive_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_12 ts SBF L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Rs_Edf_FullyPreemptive_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12 ts tsk SBF L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_16
         inst_26
         inst_23
         inst_19 PState arr_seq sched
         tsk R
```
