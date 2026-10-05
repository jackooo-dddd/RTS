# `uniprocessor_response_time_bound_fifo`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.ovh.fifo.bounded_nps.uniprocessor_response_time_bound_fifo`
- Lean: `Prosa.Results.Rta.Ovh.Fifo.BoundedNps.uniprocessor_response_time_bound_fifo`
- Certificate: `uniprocessor_response_time_bound_fifo_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fifo :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {H1 : TaskRunToCompletionThreshold Task}
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobArrival Job} 
  {H5 : JobPreemptable Job} (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall arr_seq : arrival_sequence Job,
@valid_task_arrival_sequence Task H H0 Job H2 H3 H4 ts arr_seq ->
@valid_task_run_to_completion_threshold Task H Job H2 H3 H5 H1 arr_seq tsk ->
@arrivals_have_positive_job_costs Job H3 arr_seq ->
forall sched : @schedule Job (processor_state Job),
@valid_schedule Job H4 (processor_state Job) sched H3 (@basic_ready_instance Job (processor_state Job) H4 H3)
  arr_seq ->
@work_conserving Job H4 H3 (processor_state Job) (@basic_ready_instance Job (processor_state Job) H4 H3)
  arr_seq sched ->
@valid_preemption_model Job H3 H5 (processor_state Job) arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H4 H3 (processor_state Job) H5
  (@basic_ready_instance Job (processor_state Job) H4 H3) arr_seq sched (@FIFO Job H4) ->
@no_superfluous_preemptions Job H3 (@JLFP_to_JLDP Job (@FIFO Job H4)) (processor_state Job) sched ->
forall DB CSB CRPDB : duration,
@overhead_resource_model Job sched DB CSB CRPDB ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 ts DB CSB CRPDB L ->
forall R : duration,
@rta_recurrence_solution Task H H0 ts DB CSB CRPDB L R ->
@task_response_time_bound Task Job H4 H3 H2 (processor_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_fifo is not universe polymorphic
Arguments uniprocessor_response_time_bound_fifo {Task H H0 H1 Job H2 H3 H4 H5} ts%seq_scope 
  tsk H_tsk_in_ts arr_seq H_valid_task_arrival_sequence H_valid_run_to_completion_threshold
  H_arrivals_have_positive_job_costs sched H_valid_schedule H_work_conserving H_valid_preemption_model
  H_respects_policy H_no_superfluous_preemptions DB CSB CRPDB H_valid_overheads_model 
  L _ R _ j _ _
uniprocessor_response_time_bound_fifo is opaque
Expands to: Constant prosa.results.rta.ovh.fifo.bounded_nps.uniprocessor_response_time_bound_fifo
Declared in library prosa.results.rta.ovh.fifo.bounded_nps, line 186, characters 10-47
@uniprocessor_response_time_bound_fifo
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task)
         (H1 : TaskRunToCompletionThreshold Task) (Job : JobType) (H2 : JobTask Job Task) 
         (H3 : JobCost Job) (H4 : JobArrival Job) (H5 : JobPreemptable Job) (ts : seq (Equality.sort Task))
         (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall arr_seq : arrival_sequence Job,
       @valid_task_arrival_sequence Task H H0 Job H2 H3 H4 ts arr_seq ->
       @valid_task_run_to_completion_threshold Task H Job H2 H3 H5 H1 arr_seq tsk ->
       @arrivals_have_positive_job_costs Job H3 arr_seq ->
       forall sched : @schedule Job (processor_state Job),
       @valid_schedule Job H4 (processor_state Job) sched H3
         (@basic_ready_instance Job (processor_state Job) H4 H3) arr_seq ->
       @work_conserving Job H4 H3 (processor_state Job)
         (@basic_ready_instance Job (processor_state Job) H4 H3) arr_seq sched ->
       @valid_preemption_model Job H3 H5 (processor_state Job) arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H4 H3 (processor_state Job) H5
         (@basic_ready_instance Job (processor_state Job) H4 H3) arr_seq sched (@FIFO Job H4) ->
       @no_superfluous_preemptions Job H3 (@JLFP_to_JLDP Job (@FIFO Job H4)) (processor_state Job) sched ->
       forall DB CSB CRPDB : duration,
       @overhead_resource_model Job sched DB CSB CRPDB ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 ts DB CSB CRPDB L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 ts DB CSB CRPDB L R ->
       @task_response_time_bound Task Job H4 H3 H2 (processor_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Ovh.Fifo.BoundedNps.uniprocessor_response_time_bound_fifo : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_4 : DecidableEq Job] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Behavior.Job.JobArrival Job]
  [inst_8 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
        Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
          Prosa.Model.Job.Properties.arrivals_have_positive_job_costs arr_seq →
            ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job)),
              Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                    Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                        (Prosa.Model.Priority.Fifo.FIFO Job) →
                      Prosa.Model.Preemption.Parameter.no_superfluous_preemptions sched →
                        ∀ (DB CSB CRPDB : Prosa.Behavior.Time.duration),
                          Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model sched DB CSB CRPDB →
                            ∀ (L : Prosa.Behavior.Time.duration),
                              Prosa.Results.Rta.Ovh.Fifo.BoundedNps.busy_window_recurrence_solution ts DB CSB CRPDB L →
                                ∀ (R : Prosa.Behavior.Time.duration),
                                  Prosa.Results.Rta.Ovh.Fifo.BoundedNps.rta_recurrence_solution ts DB CSB CRPDB L R →
                                    Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched tsk
                                      R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ovh_Fifo_BoundedNps_uniprocessor_response_time_bound_fifo
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
       Prosa_Model_Job_Properties_arrivals_have_positive_job_costs Job
         inst_16
         inst_23 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_16
                   (Prosa_Model_Processor_Overheads_processor_state Job
                      inst_16),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_16
         inst_26
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_16)
         sched inst_23
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_16
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_16)
            inst_26
            inst_23)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_16
         inst_26
         inst_23
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_16)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_16
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_16)
            inst_26
            inst_23)
         arr_seq sched ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_16
         inst_23
         inst_29
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_16)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_16
         inst_26
         inst_23
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_16)
         inst_29
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_16
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_16)
            inst_26
            inst_23)
         arr_seq sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_16
            inst_26) ->
       Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4 Job
         inst_16
         inst_23
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_16
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_16
               inst_26))
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_16)
         sched ->
       forall DB CSB CRPDB : Prosa_Behavior_Time_duration,
       Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model Job
         inst_16 sched DB CSB CRPDB ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Ovh_Fifo_BoundedNps_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts DB CSB CRPDB L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Ovh_Fifo_BoundedNps_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts DB CSB CRPDB L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8 Task
         inst_3 Job
         inst_16
         inst_26
         inst_23
         inst_19
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_16)
         arr_seq sched tsk R
```
