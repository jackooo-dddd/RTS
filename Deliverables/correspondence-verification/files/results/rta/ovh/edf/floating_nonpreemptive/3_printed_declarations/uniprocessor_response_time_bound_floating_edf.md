# `uniprocessor_response_time_bound_floating_edf`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.ovh.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf`
- Lean: `Prosa.Results.Rta.Ovh.Edf.FloatingNonpreemptive.uniprocessor_response_time_bound_floating_edf`
- Certificate: `uniprocessor_response_time_bound_floating_edf_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_floating_edf :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {H1 : MaxArrivals Task}
  {H2 : TaskMaxNonpreemptiveSegment Task} {Job : JobType} {H3 : JobTask Job Task} 
  {H4 : JobCost Job} {H5 : JobArrival Job} {H6 : JobPreemptionPoints Job} (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall arr_seq : arrival_sequence Job,
@valid_task_arrival_sequence Task H H1 Job H3 H4 H5 ts arr_seq ->
@valid_model_with_floating_nonpreemptive_regions Task H2 Job H3 H4 H6 arr_seq ->
@arrivals_have_positive_job_costs Job H4 arr_seq ->
forall sched : @schedule Job (processor_state Job),
@valid_schedule Job H5 (processor_state Job) sched H4 (@basic_ready_instance Job (processor_state Job) H5 H4)
  arr_seq ->
@work_conserving Job H5 H4 (processor_state Job) (@basic_ready_instance Job (processor_state Job) H5 H4)
  arr_seq sched ->
@schedule_respects_preemption_model Job (processor_state Job) (@limited_preemptive_job_model Job H6) arr_seq
  sched ->
@respects_JLFP_policy_at_preemption_point Job H5 H4 (processor_state Job)
  (@limited_preemptive_job_model Job H6) (@basic_ready_instance Job (processor_state Job) H5 H4) arr_seq
  sched (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H5 H3)) ->
@no_superfluous_preemptions Job H4
  (@JLFP_to_JLDP Job (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H5 H3))) 
  (processor_state Job) sched ->
forall DB CSB CRPDB : duration,
@overhead_resource_model Job sched DB CSB CRPDB ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 H1 H2 ts tsk DB CSB CRPDB L ->
forall R : duration,
@rta_recurrence_solution Task H H0 H1 H2 ts tsk DB CSB CRPDB L R ->
@task_response_time_bound Task Job H5 H4 H3 (processor_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_floating_edf is not universe polymorphic
Arguments uniprocessor_response_time_bound_floating_edf {Task H H0 H1 H2 Job H3 H4 H5 H6} 
  ts%seq_scope tsk H_tsk_in_ts arr_seq H_valid_task_arrival_sequence
  H_valid_task_model_with_floating_nonpreemptive_regions H_arrivals_have_positive_job_costs 
  sched H_valid_schedule H_work_conserving H_schedule_with_limited_preemptions H_respects_policy
  H_no_superfluous_preemptions DB CSB CRPDB H_valid_overheads_model L _ R _ j _ _
uniprocessor_response_time_bound_floating_edf is opaque
Expands to: Constant
            prosa.results.rta.ovh.edf.floating_nonpreemptive.uniprocessor_response_time_bound_floating_edf
Declared in library prosa.results.rta.ovh.edf.floating_nonpreemptive, line 190, characters 10-55
@uniprocessor_response_time_bound_floating_edf
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
         (H2 : TaskMaxNonpreemptiveSegment Task) (Job : JobType) (H3 : JobTask Job Task) 
         (H4 : JobCost Job) (H5 : JobArrival Job) (H6 : JobPreemptionPoints Job)
         (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall arr_seq : arrival_sequence Job,
       @valid_task_arrival_sequence Task H H1 Job H3 H4 H5 ts arr_seq ->
       @valid_model_with_floating_nonpreemptive_regions Task H2 Job H3 H4 H6 arr_seq ->
       @arrivals_have_positive_job_costs Job H4 arr_seq ->
       forall sched : @schedule Job (processor_state Job),
       @valid_schedule Job H5 (processor_state Job) sched H4
         (@basic_ready_instance Job (processor_state Job) H5 H4) arr_seq ->
       @work_conserving Job H5 H4 (processor_state Job)
         (@basic_ready_instance Job (processor_state Job) H5 H4) arr_seq sched ->
       @schedule_respects_preemption_model Job (processor_state Job) (@limited_preemptive_job_model Job H6)
         arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H5 H4 (processor_state Job)
         (@limited_preemptive_job_model Job H6) (@basic_ready_instance Job (processor_state Job) H5 H4)
         arr_seq sched (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H5 H3)) ->
       @no_superfluous_preemptions Job H4
         (@JLFP_to_JLDP Job (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H5 H3)))
         (processor_state Job) sched ->
       forall DB CSB CRPDB : duration,
       @overhead_resource_model Job sched DB CSB CRPDB ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 H1 H2 ts tsk DB CSB CRPDB L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 H1 H2 ts tsk DB CSB CRPDB L R ->
       @task_response_time_bound Task Job H5 H4 H3 (processor_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Ovh.Edf.FloatingNonpreemptive.uniprocessor_response_time_bound_floating_edf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_4 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_5 : DecidableEq Job] [inst_6 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_7 : Prosa.Behavior.Job.JobCost Job] [inst_8 : Prosa.Behavior.Job.JobArrival Job]
  [inst_9 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job] (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
        Prosa.Model.Task.Preemption.FloatingNonpreemptive.valid_model_with_floating_nonpreemptive_regions arr_seq →
          Prosa.Model.Job.Properties.arrivals_have_positive_job_costs arr_seq →
            ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job)),
              Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                  Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq sched →
                    Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                        (Prosa.Model.Priority.Edf.EDF Job) →
                      Prosa.Model.Preemption.Parameter.no_superfluous_preemptions sched →
                        ∀ (DB CSB CRPDB : Prosa.Behavior.Time.duration),
                          Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model sched DB CSB CRPDB →
                            ∀ (L : Prosa.Behavior.Time.duration),
                              Prosa.Results.Rta.Ovh.Edf.FloatingNonpreemptive.busy_window_recurrence_solution ts tsk DB
                                  CSB CRPDB L →
                                ∀ (R : Prosa.Behavior.Time.duration),
                                  Prosa.Results.Rta.Ovh.Edf.FloatingNonpreemptive.rta_recurrence_solution ts tsk DB CSB
                                      CRPDB L R →
                                    Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched tsk
                                      R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ovh_Edf_FloatingNonpreemptive_uniprocessor_response_time_bound_floating_edf
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
       Prosa_Model_Job_Properties_arrivals_have_positive_job_costs Job
         inst_19
         inst_26 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_19
                   (Prosa_Model_Processor_Overheads_processor_state Job
                      inst_19),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_19
         inst_29
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_19)
         sched inst_26
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_19
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_19)
            inst_29
            inst_26)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_19
         inst_29
         inst_26
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_19)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_19
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_19)
            inst_29
            inst_26)
         arr_seq sched ->
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model_inst4 Job
         inst_19
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_19)
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_19
            inst_32)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_19
         inst_29
         inst_26
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_19)
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_19
            inst_32)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_19
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_19)
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
       Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4 Job
         inst_19
         inst_26
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_19
            (Prosa_Model_Priority_Edf_EDF Job
               inst_19
               (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                  inst_19
                  inst_3
                  inst_9
                  inst_29
                  inst_22)))
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_19)
         sched ->
       forall DB CSB CRPDB : Prosa_Behavior_Time_duration,
       Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model Job
         inst_19 sched DB CSB
         CRPDB ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Ovh_Edf_FloatingNonpreemptive_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12
         inst_15 ts tsk DB CSB
         CRPDB L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Ovh_Edf_FloatingNonpreemptive_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12
         inst_15 ts tsk DB CSB
         CRPDB L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8 Task
         inst_3 Job
         inst_19
         inst_29
         inst_26
         inst_22
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_19)
         arr_seq sched tsk R
```
