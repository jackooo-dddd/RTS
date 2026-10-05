# `uniprocessor_response_time_bound_limited_fp`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.rs.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp`
- Lean: `Prosa.Results.Rta.Rs.Fp.LimitedPreemptive.uniprocessor_response_time_bound_limited_fp`
- Certificate: `uniprocessor_response_time_bound_limited_fp_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_limited_fp :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {H1 : TaskPreemptionPoints Task}
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobArrival Job}
  {H5 : JobPreemptionPoints Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H4 arr_seq ->
@arrivals_have_valid_job_costs Task H Job H2 H3 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
@valid_fixed_preemption_points_model Task H H1 Job H2 H3 H5 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall sched : @schedule Job PState,
@valid_schedule Job H4 PState sched H3 (@sequential_readiness Task Job H2 H3 H4 PState arr_seq) arr_seq ->
@work_conserving Job H4 H3 PState (@sequential_readiness Task Job H2 H3 H4 PState arr_seq) arr_seq sched ->
@schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H5) arr_seq sched ->
forall {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
@respects_FP_policy_at_preemption_point Task Job H2 H4 H3 PState (@limited_preemptive_job_model Job H5)
  (@sequential_readiness Task Job H2 H3 H4 PState arr_seq) arr_seq sched FP ->
forall {SBF : SupplyBoundFunction},
unit_supply_bound_function SBF ->
@valid_busy_sbf Task Job H4 H3 H2 PState arr_seq sched (@FP_to_JLFP Job Task H2 FP) tsk SBF ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 H1 ts tsk FP SBF L ->
forall R : duration,
@rta_recurrence_solution Task H H0 H1 ts tsk FP SBF L R ->
@task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R

uniprocessor_response_time_bound_limited_fp is not universe polymorphic
Arguments uniprocessor_response_time_bound_limited_fp {Task H H0 H1 Job H2 H3 H4 H5 PState}
  H_uniprocessor_proc_model H_unit_supply_proc_model H_consumed_supply_proc_model 
  arr_seq H_valid_arrival_sequence H_valid_job_cost ts%seq_scope H_all_jobs_from_taskset
  H_valid_model_with_fixed_preemption_points H_is_arrival_curve H_valid_arrival_curve 
  tsk H_tsk_in_ts sched H_valid_schedule H_work_conserving H_schedule_with_limited_preemptions 
  {FP} H_priority_is_reflexive H_priority_is_transitive H_respects_policy_at_preemption_point 
  {SBF} H_unit_SBF H_valid_SBF L _ R _ j _ _
uniprocessor_response_time_bound_limited_fp is opaque
Expands to: Constant prosa.results.rta.rs.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp
Declared in library prosa.results.rta.rs.fp.limited_preemptive, line 187, characters 10-53
@uniprocessor_response_time_bound_limited_fp
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : TaskPreemptionPoints Task)
         (Job : JobType) (H2 : JobTask Job Task) (H3 : JobCost Job) (H4 : JobArrival Job)
         (H5 : JobPreemptionPoints Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H4 arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H2 H3 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       @valid_fixed_preemption_points_model Task H H1 Job H2 H3 H5 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H4 PState sched H3 (@sequential_readiness Task Job H2 H3 H4 PState arr_seq)
         arr_seq ->
       @work_conserving Job H4 H3 PState (@sequential_readiness Task Job H2 H3 H4 PState arr_seq) arr_seq
         sched ->
       @schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H5) arr_seq sched ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       @respects_FP_policy_at_preemption_point Task Job H2 H4 H3 PState
         (@limited_preemptive_job_model Job H5) (@sequential_readiness Task Job H2 H3 H4 PState arr_seq)
         arr_seq sched FP ->
       forall SBF : SupplyBoundFunction,
       unit_supply_bound_function SBF ->
       @valid_busy_sbf Task Job H4 H3 H2 PState arr_seq sched (@FP_to_JLFP Job Task H2 FP) tsk SBF ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 H1 ts tsk FP SBF L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 H1 ts tsk FP SBF L R ->
       @task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Rs.Fp.LimitedPreemptive.uniprocessor_response_time_bound_limited_fp : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_4 : DecidableEq Job] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Behavior.Job.JobArrival Job]
  [inst_8 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
          Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
            Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
              ∀ (ts : List Task),
                Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                  Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_model arr_seq ts →
                    Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                      Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                          Prosa.Model.Task.Arrival.Curves.max_arrivals →
                        ∀ (tsk : Task),
                          decide (tsk ∈ ts) = true →
                            ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                              Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                                Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                                  Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq
                                      sched →
                                    ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
                                      Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
                                        Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
                                          Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point
                                              arr_seq sched FP →
                                            ∀ (SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction),
                                              Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
                                                  Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                                Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf arr_seq sched tsk
                                                    Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
                                                  ∀ (L : Prosa.Behavior.Time.duration),
                                                    Prosa.Results.Rta.Rs.Fp.LimitedPreemptive.busy_window_recurrence_solution
                                                        ts tsk SBF L →
                                                      ∀ (R : Prosa.Behavior.Time.duration),
                                                        Prosa.Results.Rta.Rs.Fp.LimitedPreemptive.rta_recurrence_solution
                                                            ts tsk SBF L R →
                                                          Prosa.Analysis.Definitions.Schedulability.task_response_time_bound
                                                            arr_seq sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Rs_Fp_LimitedPreemptive_uniprocessor_response_time_bound_limited_fp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_12 : 
          Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
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
         (inst_29 : 
          Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
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
       Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_model Task
         inst_3
         inst_6
         inst_12 Job
         inst_16
         inst_19
         inst_23
         inst_29 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_16
         inst_19 arr_seq
         inst_9 ts ->
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_9) ->
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
         (Prosa_Model_Readiness_Sequential_sequential_ready_instance Job
            inst_16 Task
            inst_3
            inst_19
            inst_26
            inst_23 PState arr_seq)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_16
         inst_26
         inst_23 PState
         (Prosa_Model_Readiness_Sequential_sequential_ready_instance Job
            inst_16 Task
            inst_3
            inst_19
            inst_26
            inst_23 PState arr_seq)
         arr_seq sched ->
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model Job
         inst_16 PState
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_16
            inst_29)
         arr_seq sched ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point Task
         inst_3 Job
         inst_16
         inst_19
         inst_26
         inst_23 PState
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_16
            inst_29)
         (Prosa_Model_Readiness_Sequential_sequential_ready_instance Job
            inst_16 Task
            inst_3
            inst_19
            inst_26
            inst_23 PState arr_seq)
         arr_seq sched FP ->
       forall SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction,
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf Task
         inst_3 Job
         inst_16
         inst_26
         inst_23
         inst_19 PState arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_16 Task
            inst_3
            inst_19 FP)
         tsk (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Rs_Fp_LimitedPreemptive_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12 ts tsk FP SBF L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Rs_Fp_LimitedPreemptive_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12 ts tsk FP SBF L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_16
         inst_26
         inst_23
         inst_19 PState arr_seq sched
         tsk R
```
