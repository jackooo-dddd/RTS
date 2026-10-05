# `uniprocessor_response_time_bound_fifo`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.arm.fifo.bounded_nps.uniprocessor_response_time_bound_fifo`
- Lean: `Prosa.Results.Rta.Arm.Fifo.BoundedNps.uniprocessor_response_time_bound_fifo`
- Certificate: `uniprocessor_response_time_bound_fifo_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fifo :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {H1 : TaskRunToCompletionThreshold Task}
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobArrival Job} 
  {H5 : JobPreemptable Job} (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_task_arrival_sequence Task H H0 Job H2 H3 H4 ts arr_seq ->
@valid_task_run_to_completion_threshold Task H Job H2 H3 H5 H1 arr_seq tsk ->
forall sched : @schedule Job PState,
@valid_schedule Job H4 PState sched H3 (@basic_ready_instance Job PState H4 H3) arr_seq ->
@work_conserving Job H4 H3 PState (@basic_ready_instance Job PState H4 H3) arr_seq sched ->
@valid_preemption_model Job H3 H5 PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H4 H3 PState H5 (@basic_ready_instance Job PState H4 H3)
  arr_seq sched (@FIFO Job H4) ->
forall Π Θ ν : duration,
@average_resource_model Job PState Π Θ ν sched ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 ts Π Θ ν L ->
forall R : duration,
@rta_recurrence_solution Task H H0 ts Π Θ ν L R ->
@task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R

uniprocessor_response_time_bound_fifo is not universe polymorphic
Arguments uniprocessor_response_time_bound_fifo {Task H H0 H1 Job H2 H3 H4 H5} ts%seq_scope 
  tsk H_tsk_in_ts {PState} H_uniprocessor_proc_model H_unit_supply_proc_model H_consumed_supply_proc_model
  arr_seq H_valid_task_arrival_sequence H_valid_run_to_completion_threshold sched 
  H_valid_schedule H_work_conserving H_valid_preemption_model H_respects_policy Π 
  Θ ν H_average_resource_model L _ R _ j _ _
uniprocessor_response_time_bound_fifo is opaque
Expands to: Constant prosa.results.rta.arm.fifo.bounded_nps.uniprocessor_response_time_bound_fifo
Declared in library prosa.results.rta.arm.fifo.bounded_nps, line 162, characters 10-47
@uniprocessor_response_time_bound_fifo
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task)
         (H1 : TaskRunToCompletionThreshold Task) (Job : JobType) (H2 : JobTask Job Task) 
         (H3 : JobCost Job) (H4 : JobArrival Job) (H5 : JobPreemptable Job) (ts : seq (Equality.sort Task))
         (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_task_arrival_sequence Task H H0 Job H2 H3 H4 ts arr_seq ->
       @valid_task_run_to_completion_threshold Task H Job H2 H3 H5 H1 arr_seq tsk ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H4 PState sched H3 (@basic_ready_instance Job PState H4 H3) arr_seq ->
       @work_conserving Job H4 H3 PState (@basic_ready_instance Job PState H4 H3) arr_seq sched ->
       @valid_preemption_model Job H3 H5 PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H4 H3 PState H5 (@basic_ready_instance Job PState H4 H3)
         arr_seq sched (@FIFO Job H4) ->
       forall Π Θ ν : duration,
       @average_resource_model Job PState Π Θ ν sched ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 ts Π Θ ν L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 ts Π Θ ν L R ->
       @task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Arm.Fifo.BoundedNps.uniprocessor_response_time_bound_fifo : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_4 : DecidableEq Job] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Behavior.Job.JobArrival Job]
  [inst_8 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
          Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
                Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
                  ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                    Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                        Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                          Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                              (Prosa.Model.Priority.Fifo.FIFO Job) →
                            ∀ (Pi Θ ν : Prosa.Behavior.Time.duration),
                              Prosa.Analysis.Definitions.Sbf.Average.average_resource_model Pi Θ ν sched →
                                ∀ (L : Prosa.Behavior.Time.duration),
                                  Prosa.Results.Rta.Arm.Fifo.BoundedNps.busy_window_recurrence_solution ts Pi Θ ν L →
                                    ∀ (R : Prosa.Behavior.Time.duration),
                                      Prosa.Results.Rta.Arm.Fifo.BoundedNps.rta_recurrence_solution ts Pi Θ ν L R →
                                        Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched
                                          tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Arm_Fifo_BoundedNps_uniprocessor_response_time_bound_fifo
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_12 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
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
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_16)
         (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_16,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_16 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_16 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_16 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_16,
       Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence Task
         inst_3
         inst_6
         inst_9 Job
         inst_16
         inst_19
         inst_23
         inst_26 ts arr_seq ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_6 Job
         inst_16
         inst_19
         inst_23
         inst_29
         inst_12 arr_seq tsk ->
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
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_16
         inst_23
         inst_29 PState arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_16
         inst_26
         inst_23 PState
         inst_29
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_16 PState
            inst_26
            inst_23)
         arr_seq sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_16
            inst_26) ->
       forall Pi _UU0398_ _UU03bd_ : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_Sbf_Average_average_resource_model Job
         inst_16 PState Pi _UU0398_
         _UU03bd_ sched ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Arm_Fifo_BoundedNps_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts Pi _UU0398_ _UU03bd_ L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Arm_Fifo_BoundedNps_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts Pi _UU0398_ _UU03bd_ L
         R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_16
         inst_26
         inst_23
         inst_19 PState arr_seq sched tsk
         R
```
