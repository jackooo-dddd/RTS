# `uniprocessor_response_time_bound_limited_fp`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.prm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp`
- Lean: `Prosa.Results.Rta.Prm.Fp.LimitedPreemptive.uniprocessor_response_time_bound_limited_fp`
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
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall arr_seq : arrival_sequence Job,
@valid_task_arrival_sequence Task H H0 Job H2 H3 H4 ts arr_seq ->
@valid_fixed_preemption_points_model Task H H1 Job H2 H3 H5 arr_seq ts ->
forall {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
forall sched : @schedule Job PState,
@valid_schedule Job H4 PState sched H3 (@basic.basic_ready_instance Job PState H4 H3) arr_seq ->
@work_conserving Job H4 H3 PState (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched ->
@schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H5) arr_seq sched ->
@respects_FP_policy_at_preemption_point Task Job H2 H4 H3 PState (@limited_preemptive_job_model Job H5)
  (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched FP ->
@sequential_tasks Job Task H2 H4 H3 PState arr_seq sched ->
forall Π γ : duration,
@periodic_resource_model Job PState Π γ sched ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 H1 ts tsk FP Π γ L ->
forall R : duration,
@rta_recurrence_solution Task H H0 H1 ts tsk FP Π γ L R ->
@task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R

uniprocessor_response_time_bound_limited_fp is not universe polymorphic
Arguments uniprocessor_response_time_bound_limited_fp {Task H H0 H1 Job H2 H3 H4 H5 PState}
  H_uniprocessor_proc_model H_unit_supply_proc_model H_consumed_supply_proc_model 
  ts%seq_scope tsk H_tsk_in_ts arr_seq H_valid_task_arrival_sequence
  H_valid_model_with_fixed_preemption_points {FP} H_priority_is_reflexive H_priority_is_transitive 
  sched H_valid_schedule H_work_conserving H_schedule_with_limited_preemptions H_respects_policy
  H_sequential_tasks Π γ H_periodic_resource_model L _ R _ j _ _
uniprocessor_response_time_bound_limited_fp is opaque
Expands to: Constant prosa.results.rta.prm.fp.limited_preemptive.uniprocessor_response_time_bound_limited_fp
Declared in library prosa.results.rta.prm.fp.limited_preemptive, line 172, characters 10-53
@uniprocessor_response_time_bound_limited_fp
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : TaskPreemptionPoints Task)
         (Job : JobType) (H2 : JobTask Job Task) (H3 : JobCost Job) (H4 : JobArrival Job)
         (H5 : JobPreemptionPoints Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall arr_seq : arrival_sequence Job,
       @valid_task_arrival_sequence Task H H0 Job H2 H3 H4 ts arr_seq ->
       @valid_fixed_preemption_points_model Task H H1 Job H2 H3 H5 arr_seq ts ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H4 PState sched H3 (@basic.basic_ready_instance Job PState H4 H3) arr_seq ->
       @work_conserving Job H4 H3 PState (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched ->
       @schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H5) arr_seq sched ->
       @respects_FP_policy_at_preemption_point Task Job H2 H4 H3 PState
         (@limited_preemptive_job_model Job H5) (@basic.basic_ready_instance Job PState H4 H3) arr_seq sched
         FP ->
       @sequential_tasks Job Task H2 H4 H3 PState arr_seq sched ->
       forall Π γ : duration,
       @periodic_resource_model Job PState Π γ sched ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 H1 ts tsk FP Π γ L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 H1 ts tsk FP Π γ L R ->
       @task_response_time_bound Task Job H4 H3 H2 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Prm.Fp.LimitedPreemptive.uniprocessor_response_time_bound_limited_fp : ∀
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
        ∀ (ts : List Task) (tsk : Task),
          decide (tsk ∈ ts) = true →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
                Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_model arr_seq ts →
                  ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
                    Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
                      Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
                        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                            Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                              Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq sched →
                                Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched
                                    FP →
                                  Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                                    ∀ (Pi γ : Prosa.Behavior.Time.duration),
                                      Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model Pi γ sched →
                                        ∀ (L : Prosa.Behavior.Time.duration),
                                          Prosa.Results.Rta.Prm.Fp.LimitedPreemptive.busy_window_recurrence_solution ts
                                              tsk Pi γ L →
                                            ∀ (R : Prosa.Behavior.Time.duration),
                                              Prosa.Results.Rta.Prm.Fp.LimitedPreemptive.rta_recurrence_solution ts tsk
                                                  Pi γ L R →
                                                Prosa.Analysis.Definitions.Schedulability.task_response_time_bound
                                                  arr_seq sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Prm_Fp_LimitedPreemptive_uniprocessor_response_time_bound_limited_fp
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
         inst_9 Job
         inst_16
         inst_19
         inst_23
         inst_26 ts arr_seq ->
       Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_model Task
         inst_3
         inst_6
         inst_12 Job
         inst_16
         inst_19
         inst_23
         inst_29 arr_seq ts ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
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
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model Job
         inst_16 PState
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_16
            inst_29)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point Task
         inst_3 Job
         inst_16
         inst_19
         inst_26
         inst_23 PState
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_16
            inst_29)
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_16 PState
            inst_26
            inst_23)
         arr_seq sched FP ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_16 Task
         inst_3
         inst_19
         inst_26
         inst_23 PState arr_seq
         sched ->
       forall Pi _UU03b3_ : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model Job
         inst_16 PState Pi _UU03b3_
         sched ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Prm_Fp_LimitedPreemptive_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12 ts tsk FP Pi
         _UU03b3_ L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Prm_Fp_LimitedPreemptive_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9
         inst_12 ts tsk FP Pi
         _UU03b3_ L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_16
         inst_26
         inst_23
         inst_19 PState arr_seq
         sched tsk R
```
