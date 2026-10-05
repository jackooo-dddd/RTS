# `uniprocessor_response_time_bound_fully_nonpreemptive_edf`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.prm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf`
- Lean: `Prosa.Results.Rta.Prm.Edf.FullyNonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf`
- Certificate: `uniprocessor_response_time_bound_fully_nonpreemptive_edf_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fully_nonpreemptive_edf :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {H1 : MaxArrivals Task} 
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobArrival Job}
  {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall arr_seq : arrival_sequence Job,
@valid_task_arrival_sequence Task H H1 Job H2 H3 H4 ts arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job H4 PState sched H3 (@basic.basic_ready_instance Job PState H4 H3) arr_seq ->
@work_conserving Job H4 H3 PState (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched ->
@nonpreemptive_schedule Job H3 PState sched ->
@respects_JLFP_policy_at_preemption_point Job H4 H3 PState (@fully_nonpreemptive_job_model Job H3)
  (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H4 H2)) ->
forall Π γ : duration,
@periodic_resource_model Job PState Π γ sched ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 H1 ts tsk Π γ L ->
forall R : duration,
@rta_recurrence_solution Task H H0 H1 ts tsk Π γ L R ->
@task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R

uniprocessor_response_time_bound_fully_nonpreemptive_edf is not universe polymorphic
Arguments uniprocessor_response_time_bound_fully_nonpreemptive_edf {Task H H0 H1 Job H2 H3 H4 PState}
  H_uniprocessor_proc_model H_unit_supply_proc_model H_consumed_supply_proc_model 
  ts%seq_scope tsk H_tsk_in_ts arr_seq H_valid_task_arrival_sequence sched H_valid_schedule 
  H_work_conserving H_nonpreemptive_sched H_respects_policy Π γ H_periodic_resource_model 
  L _ R _ j _ _
uniprocessor_response_time_bound_fully_nonpreemptive_edf is opaque
Expands to: Constant
            prosa.results.rta.prm.edf.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf
Declared in library prosa.results.rta.prm.edf.fully_nonpreemptive, line 160, characters 10-66
@uniprocessor_response_time_bound_fully_nonpreemptive_edf
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
         (Job : JobType) (H2 : JobTask Job Task) (H3 : JobCost Job) (H4 : JobArrival Job)
         (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall arr_seq : arrival_sequence Job,
       @valid_task_arrival_sequence Task H H1 Job H2 H3 H4 ts arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H4 PState sched H3 (@basic.basic_ready_instance Job PState H4 H3) arr_seq ->
       @work_conserving Job H4 H3 PState (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched ->
       @nonpreemptive_schedule Job H3 PState sched ->
       @respects_JLFP_policy_at_preemption_point Job H4 H3 PState (@fully_nonpreemptive_job_model Job H3)
         (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H4 H2)) ->
       forall Π γ : duration,
       @periodic_resource_model Job PState Π γ sched ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 H1 ts tsk Π γ L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 H1 ts tsk Π γ L R ->
       @task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Prm.Edf.FullyNonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_edf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_4 : DecidableEq Job] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
        ∀ (ts : List Task) (tsk : Task),
          decide (tsk ∈ ts) = true →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
                ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                    Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                      Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule sched →
                        Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                            (Prosa.Model.Priority.Edf.EDF Job) →
                          ∀ (Pi γ : Prosa.Behavior.Time.duration),
                            Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model Pi γ sched →
                              ∀ (L : Prosa.Behavior.Time.duration),
                                Prosa.Results.Rta.Prm.Edf.FullyNonpreemptive.busy_window_recurrence_solution ts tsk Pi γ
                                    L →
                                  ∀ (R : Prosa.Behavior.Time.duration),
                                    Prosa.Results.Rta.Prm.Edf.FullyNonpreemptive.rta_recurrence_solution ts tsk Pi γ L
                                        R →
                                      Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched
                                        tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Prm_Edf_FullyNonpreemptive_uniprocessor_response_time_bound_fully_nonpreemptive_edf
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
         (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : 
          DecidableEq Job)
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
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_16,
       Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence Task
         inst_3
         inst_6
         inst_12 Job
         inst_16
         inst_19
         inst_23
         inst_26 ts arr_seq ->
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
       Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule Job
         inst_16
         inst_23 PState sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_16
         inst_26
         inst_23 PState
         (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
            inst_16
            inst_23)
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
       forall Pi _UU03b3_ : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model Job
         inst_16 PState Pi
         _UU03b3_ sched ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Prm_Edf_FullyNonpreemptive_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12 ts tsk Pi
         _UU03b3_ L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Prm_Edf_FullyNonpreemptive_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12 ts tsk Pi
         _UU03b3_ L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_16
         inst_26
         inst_23
         inst_19 PState arr_seq
         sched tsk R
```
