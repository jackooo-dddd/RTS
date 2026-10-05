# `uniprocessor_response_time_bound_floating_edf`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.arm.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf`
- Lean: `Prosa.Results.Rta.Arm.Edf.FloatingNonpreemptive.uniprocessor_response_time_bound_floating_edf`
- Certificate: `uniprocessor_response_time_bound_floating_edf_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_floating_edf :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {H1 : MaxArrivals Task}
  {H2 : TaskMaxNonpreemptiveSegment Task} {Job : JobType} {H3 : JobTask Job Task} 
  {H4 : JobCost Job} {H5 : JobArrival Job} {H6 : JobPreemptionPoints Job} (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_task_arrival_sequence Task H H1 Job H3 H4 H5 ts arr_seq ->
@valid_model_with_floating_nonpreemptive_regions Task H2 Job H3 H4 H6 arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job H5 PState sched H4 (@basic.basic_ready_instance Job PState H5 H4) arr_seq ->
@work_conserving Job H5 H4 PState (@basic.basic_ready_instance Job PState H5 H4) arr_seq sched ->
@schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H6) arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H5 H4 PState (@limited_preemptive_job_model Job H6)
  (@basic.basic_ready_instance Job PState H5 H4) arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H5 H3)) ->
forall Π Θ ν : duration,
@average_resource_model Job PState Π Θ ν sched ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 H1 H2 ts tsk Π Θ ν L ->
forall R : duration,
@rta_recurrence_solution Task H H0 H1 H2 ts tsk Π Θ ν L R ->
@task_response_time_bound Task Job H5 H4 H3 PState arr_seq sched tsk R

uniprocessor_response_time_bound_floating_edf is not universe polymorphic
Arguments uniprocessor_response_time_bound_floating_edf {Task H H0 H1 H2 Job H3 H4 H5 H6} 
  ts%seq_scope tsk H_tsk_in_ts {PState} H_uniprocessor_proc_model H_unit_supply_proc_model
  H_consumed_supply_proc_model arr_seq H_valid_task_arrival_sequence
  H_valid_task_model_with_floating_nonpreemptive_regions sched H_valid_schedule H_work_conserving
  H_schedule_with_limited_preemptions H_respects_policy Π Θ ν H_average_resource_model 
  L _ R _ j _ _
uniprocessor_response_time_bound_floating_edf is opaque
Expands to: Constant
            prosa.results.rta.arm.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf
Declared in library prosa.results.rta.arm.edf.floating_nonpreemptive, line 168, characters 10-55
@uniprocessor_response_time_bound_floating_edf
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
         (H2 : TaskMaxNonpreemptiveSegment Task) (Job : JobType) (H3 : JobTask Job Task) 
         (H4 : JobCost Job) (H5 : JobArrival Job) (H6 : JobPreemptionPoints Job)
         (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_task_arrival_sequence Task H H1 Job H3 H4 H5 ts arr_seq ->
       @valid_model_with_floating_nonpreemptive_regions Task H2 Job H3 H4 H6 arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H5 PState sched H4 (@basic.basic_ready_instance Job PState H5 H4) arr_seq ->
       @work_conserving Job H5 H4 PState (@basic.basic_ready_instance Job PState H5 H4) arr_seq sched ->
       @schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H6) arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H5 H4 PState (@limited_preemptive_job_model Job H6)
         (@basic.basic_ready_instance Job PState H5 H4) arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H5 H3)) ->
       forall Π Θ ν : duration,
       @average_resource_model Job PState Π Θ ν sched ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 H1 H2 ts tsk Π Θ ν L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 H1 H2 ts tsk Π Θ ν L R ->
       @task_response_time_bound Task Job H5 H4 H3 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Arm.Edf.FloatingNonpreemptive.uniprocessor_response_time_bound_floating_edf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_4 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_5 : DecidableEq Job] [inst_6 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_7 : Prosa.Behavior.Job.JobCost Job] [inst_8 : Prosa.Behavior.Job.JobArrival Job]
  [inst_9 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
          Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
                Prosa.Model.Task.Preemption.FloatingNonpreemptive.valid_model_with_floating_nonpreemptive_regions
                    arr_seq →
                  ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                    Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                        Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq sched →
                          Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                              (Prosa.Model.Priority.Edf.EDF Job) →
                            ∀ (Pi Θ ν : Prosa.Behavior.Time.duration),
                              Prosa.Analysis.Definitions.Sbf.Average.average_resource_model Pi Θ ν sched →
                                ∀ (L : Prosa.Behavior.Time.duration),
                                  Prosa.Results.Rta.Arm.Edf.FloatingNonpreemptive.busy_window_recurrence_solution ts tsk
                                      Pi Θ ν L →
                                    ∀ (R : Prosa.Behavior.Time.duration),
                                      Prosa.Results.Rta.Arm.Edf.FloatingNonpreemptive.rta_recurrence_solution ts tsk Pi
                                          Θ ν L R →
                                        Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched
                                          tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Arm_Edf_FloatingNonpreemptive_uniprocessor_response_time_bound_floating_edf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3)
         (inst_12 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_15 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_19 : 
          DecidableEq Job)
         (inst_22 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_19 Task
            inst_3)
         (inst_26 : 
          Prosa_Behavior_Job_JobCost Job
            inst_19)
         (inst_29 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_19)
         (inst_32 : 
          Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
            inst_19)
         (ts : List Task) (tsk : Task),
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
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_19,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_19 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_19 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_19 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_19,
       Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence Task
         inst_3
         inst_6
         inst_12 Job
         inst_19
         inst_22
         inst_26
         inst_29 ts arr_seq ->
       Prosa_Model_Task_Preemption_FloatingNonpreemptive_valid_model_with_floating_nonpreemptive_regions Task
         inst_3
         inst_15 Job
         inst_19
         inst_22
         inst_26
         inst_32 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_19
                   PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_19
         inst_29 PState sched
         inst_26
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_19 PState
            inst_29
            inst_26)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_19
         inst_29
         inst_26 PState
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_19 PState
            inst_29
            inst_26)
         arr_seq sched ->
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model Job
         inst_19 PState
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_19
            inst_32)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_19
         inst_29
         inst_26 PState
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_19
            inst_32)
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_19 PState
            inst_29
            inst_26)
         arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_19
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_19
               inst_3
               inst_9
               inst_29
               inst_22)) ->
       forall Pi _UU0398_ _UU03bd_ : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_Sbf_Average_average_resource_model Job
         inst_19 PState Pi
         _UU0398_ _UU03bd_ sched ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Arm_Edf_FloatingNonpreemptive_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12
         inst_15 ts tsk Pi
         _UU0398_ _UU03bd_ L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Arm_Edf_FloatingNonpreemptive_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12
         inst_15 ts tsk Pi
         _UU0398_ _UU03bd_ L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_19
         inst_29
         inst_26
         inst_22 PState arr_seq
         sched tsk R
```
