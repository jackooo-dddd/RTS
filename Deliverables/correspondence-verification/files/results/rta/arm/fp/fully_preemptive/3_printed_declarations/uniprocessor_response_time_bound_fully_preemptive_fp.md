# `uniprocessor_response_time_bound_fully_preemptive_fp`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.arm.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp`
- Lean: `Prosa.Results.Rta.Arm.Fp.FullyPreemptive.uniprocessor_response_time_bound_fully_preemptive_fp`
- Certificate: `uniprocessor_response_time_bound_fully_preemptive_fp_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fully_preemptive_fp :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H2 : JobCost Job} {H3 : JobArrival Job} (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
@fully_consuming_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_task_arrival_sequence Task H H0 Job H1 H2 H3 ts arr_seq ->
forall {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
forall sched : @schedule Job PState,
@valid_schedule Job H3 PState sched H2 (@basic.basic_ready_instance Job PState H3 H2) arr_seq ->
@work_conserving Job H3 H2 PState (@basic.basic_ready_instance Job PState H3 H2) arr_seq sched ->
@respects_FP_policy_at_preemption_point Task Job H1 H3 H2 PState (@fully_preemptive_job_model Job)
  (@basic.basic_ready_instance Job PState H3 H2) arr_seq sched FP ->
@sequential_tasks Job Task H1 H3 H2 PState arr_seq sched ->
forall Π Θ ν : duration,
@average_resource_model Job PState Π Θ ν sched ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 ts tsk FP Π Θ ν L ->
forall R : duration,
@rta_recurrence_solution Task H H0 ts tsk FP Π Θ ν L R ->
@task_response_time_bound Task Job H3 H2 H1 PState arr_seq sched tsk R

uniprocessor_response_time_bound_fully_preemptive_fp is not universe polymorphic
Arguments uniprocessor_response_time_bound_fully_preemptive_fp {Task H H0 Job H1 H2 H3} 
  ts%seq_scope tsk H_tsk_in_ts {PState} H_uniprocessor_proc_model H_unit_supply_proc_model
  H_consumed_supply_proc_model arr_seq H_valid_task_arrival_sequence {FP} H_priority_is_reflexive
  H_priority_is_transitive sched H_valid_schedule H_work_conserving H_respects_policy 
  H_sequential_tasks Π Θ ν H_average_resource_model L _ R _ j _ _
uniprocessor_response_time_bound_fully_preemptive_fp is opaque
Expands to: Constant
            prosa.results.rta.arm.fp.fully_preemptive.uniprocessor_response_time_bound_fully_preemptive_fp
Declared in library prosa.results.rta.arm.fp.fully_preemptive, line 162, characters 10-62
@uniprocessor_response_time_bound_fully_preemptive_fp
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobCost Job) (H3 : JobArrival Job) (ts : seq (Equality.sort Task))
         (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       @fully_consuming_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_task_arrival_sequence Task H H0 Job H1 H2 H3 ts arr_seq ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H3 PState sched H2 (@basic.basic_ready_instance Job PState H3 H2) arr_seq ->
       @work_conserving Job H3 H2 PState (@basic.basic_ready_instance Job PState H3 H2) arr_seq sched ->
       @respects_FP_policy_at_preemption_point Task Job H1 H3 H2 PState (@fully_preemptive_job_model Job)
         (@basic.basic_ready_instance Job PState H3 H2) arr_seq sched FP ->
       @sequential_tasks Job Task H1 H3 H2 PState arr_seq sched ->
       forall Π Θ ν : duration,
       @average_resource_model Job PState Π Θ ν sched ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 ts tsk FP Π Θ ν L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 ts tsk FP Π Θ ν L R ->
       @task_response_time_bound Task Job H3 H2 H1 PState arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Arm.Fp.FullyPreemptive.uniprocessor_response_time_bound_fully_preemptive_fp : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] [inst_6 : Prosa.Behavior.Job.JobArrival Job] (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
          Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
            ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
              Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
                ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
                  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
                    Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
                      ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
                        Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                          Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                            Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched
                                FP →
                              Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                                ∀ (Pi Θ ν : Prosa.Behavior.Time.duration),
                                  Prosa.Analysis.Definitions.Sbf.Average.average_resource_model Pi Θ ν sched →
                                    ∀ (L : Prosa.Behavior.Time.duration),
                                      Prosa.Results.Rta.Arm.Fp.FullyPreemptive.busy_window_recurrence_solution ts tsk Pi
                                          Θ ν L →
                                        ∀ (R : Prosa.Behavior.Time.duration),
                                          Prosa.Results.Rta.Arm.Fp.FullyPreemptive.rta_recurrence_solution ts tsk Pi Θ ν
                                              L R →
                                            Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq
                                              sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Arm_Fp_FullyPreemptive_uniprocessor_response_time_bound_fully_preemptive_fp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
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
                    inst_13,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_13 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_13 PState ->
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_13 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_13,
       Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence Task
         inst_3
         inst_6
         inst_9 Job
         inst_13
         inst_16
         inst_20
         inst_23 ts arr_seq ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_13 PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_13
         inst_23 PState sched
         inst_20
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_13 PState
            inst_23
            inst_20)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_13
         inst_23
         inst_20 PState
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_13 PState
            inst_23
            inst_20)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point Task
         inst_3 Job
         inst_13
         inst_16
         inst_23
         inst_20 PState
         (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job
            inst_13)
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_13 PState
            inst_23
            inst_20)
         arr_seq sched FP ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_13 Task
         inst_3
         inst_16
         inst_23
         inst_20 PState arr_seq sched ->
       forall Pi _UU0398_ _UU03bd_ : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_Sbf_Average_average_resource_model Job
         inst_13 PState Pi _UU0398_
         _UU03bd_ sched ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Arm_Fp_FullyPreemptive_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts tsk FP Pi _UU0398_
         _UU03bd_ L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Arm_Fp_FullyPreemptive_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts tsk FP Pi _UU0398_
         _UU03bd_ L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_13
         inst_23
         inst_20
         inst_16 PState arr_seq sched
         tsk R
```
