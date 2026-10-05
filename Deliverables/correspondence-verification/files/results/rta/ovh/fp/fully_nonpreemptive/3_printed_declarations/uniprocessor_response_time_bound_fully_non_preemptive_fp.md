# `uniprocessor_response_time_bound_fully_non_preemptive_fp`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.ovh.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp`
- Lean: `Prosa.Results.Rta.Ovh.Fp.FullyNonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp`
- Certificate: `uniprocessor_response_time_bound_fully_non_preemptive_fp_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fully_non_preemptive_fp :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H2 : JobCost Job} {H3 : JobArrival Job} (ts : seq (Equality.sort Task))
  (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall arr_seq : arrival_sequence Job,
@valid_task_arrival_sequence Task H H0 Job H1 H2 H3 ts arr_seq ->
@arrivals_have_positive_job_costs Job H2 arr_seq ->
forall {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
forall sched : @schedule Job (processor_state Job),
@valid_schedule Job H3 (processor_state Job) sched H2 (@basic_ready_instance Job (processor_state Job) H3 H2)
  arr_seq ->
@work_conserving Job H3 H2 (processor_state Job) (@basic_ready_instance Job (processor_state Job) H3 H2)
  arr_seq sched ->
@nonpreemptive_schedule Job H2 (processor_state Job) sched ->
@respects_FP_policy_at_preemption_point Task Job H1 H3 H2 (processor_state Job)
  (@fully_nonpreemptive_job_model Job H2) (@basic_ready_instance Job (processor_state Job) H3 H2) arr_seq
  sched FP ->
@sequential_tasks Job Task H1 H3 H2 (processor_state Job) arr_seq sched ->
@no_superfluous_preemptions Job H2 (@JLFP_to_JLDP Job (@FP_to_JLFP Job Task H1 FP)) 
  (processor_state Job) sched ->
forall DB CSB CRPDB : duration,
@overhead_resource_model Job sched DB CSB CRPDB ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 ts tsk FP DB CSB CRPDB L ->
forall R : duration,
@rta_recurrence_solution Task H H0 ts tsk FP DB CSB CRPDB L R ->
@task_response_time_bound Task Job H3 H2 H1 (processor_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_fully_non_preemptive_fp is not universe polymorphic
Arguments uniprocessor_response_time_bound_fully_non_preemptive_fp {Task H H0 Job H1 H2 H3} 
  ts%seq_scope tsk H_tsk_in_ts arr_seq H_valid_task_arrival_sequence H_arrivals_have_positive_job_costs 
  {FP} H_priority_is_reflexive H_priority_is_transitive sched H_valid_schedule H_work_conserving
  H_nonpreemptive_sched H_respects_policy H_sequential_tasks H_no_superfluous_preemptions 
  DB CSB CRPDB H_valid_overheads_model L _ R _ j _ _
uniprocessor_response_time_bound_fully_non_preemptive_fp is opaque
Expands to: Constant
            prosa.results.rta.ovh.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp
Declared in library prosa.results.rta.ovh.fp.fully_nonpreemptive, line 195, characters 10-66
@uniprocessor_response_time_bound_fully_non_preemptive_fp
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobCost Job) (H3 : JobArrival Job) (ts : seq (Equality.sort Task))
         (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall arr_seq : arrival_sequence Job,
       @valid_task_arrival_sequence Task H H0 Job H1 H2 H3 ts arr_seq ->
       @arrivals_have_positive_job_costs Job H2 arr_seq ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       forall sched : @schedule Job (processor_state Job),
       @valid_schedule Job H3 (processor_state Job) sched H2
         (@basic_ready_instance Job (processor_state Job) H3 H2) arr_seq ->
       @work_conserving Job H3 H2 (processor_state Job)
         (@basic_ready_instance Job (processor_state Job) H3 H2) arr_seq sched ->
       @nonpreemptive_schedule Job H2 (processor_state Job) sched ->
       @respects_FP_policy_at_preemption_point Task Job H1 H3 H2 (processor_state Job)
         (@fully_nonpreemptive_job_model Job H2) (@basic_ready_instance Job (processor_state Job) H3 H2)
         arr_seq sched FP ->
       @sequential_tasks Job Task H1 H3 H2 (processor_state Job) arr_seq sched ->
       @no_superfluous_preemptions Job H2 (@JLFP_to_JLDP Job (@FP_to_JLFP Job Task H1 FP))
         (processor_state Job) sched ->
       forall DB CSB CRPDB : duration,
       @overhead_resource_model Job sched DB CSB CRPDB ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 ts tsk FP DB CSB CRPDB L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 ts tsk FP DB CSB CRPDB L R ->
       @task_response_time_bound Task Job H3 H2 H1 (processor_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Ovh.Fp.FullyNonpreemptive.uniprocessor_response_time_bound_fully_non_preemptive_fp : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] [inst_6 : Prosa.Behavior.Job.JobArrival Job] (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
        Prosa.Model.Job.Properties.arrivals_have_positive_job_costs arr_seq →
          ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
            Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
              Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
                ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job)),
                  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                    Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                      Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule sched →
                        Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched FP →
                          Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                            Prosa.Model.Preemption.Parameter.no_superfluous_preemptions sched →
                              ∀ (DB CSB CRPDB : Prosa.Behavior.Time.duration),
                                Prosa.Model.Processor.OverheadResourceModel.overhead_resource_model sched DB CSB CRPDB →
                                  ∀ (L : Prosa.Behavior.Time.duration),
                                    Prosa.Results.Rta.Ovh.Fp.FullyNonpreemptive.busy_window_recurrence_solution ts tsk
                                        DB CSB CRPDB L →
                                      ∀ (R : Prosa.Behavior.Time.duration),
                                        Prosa.Results.Rta.Ovh.Fp.FullyNonpreemptive.rta_recurrence_solution ts tsk DB
                                            CSB CRPDB L R →
                                          Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq
                                            sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ovh_Fp_FullyNonpreemptive_uniprocessor_response_time_bound_fully_non_preemptive_fp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job)
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
       Prosa_Model_Job_Properties_arrivals_have_positive_job_costs Job
         inst_13
         inst_20 arr_seq ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_13
                   (Prosa_Model_Processor_Overheads_processor_state Job
                      inst_13),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_13
         inst_23
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_13)
         sched inst_20
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_13
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_13)
            inst_23
            inst_20)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_13
         inst_23
         inst_20
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_13)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_13
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_13)
            inst_23
            inst_20)
         arr_seq sched ->
       Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule_inst4 Job
         inst_13
         inst_20
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_13)
         sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point_inst8 Task
         inst_3 Job
         inst_13
         inst_16
         inst_23
         inst_20
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_13)
         (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
            inst_13
            inst_20)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_13
            (Prosa_Model_Processor_Overheads_processor_state Job
               inst_13)
            inst_23
            inst_20)
         arr_seq sched FP ->
       Prosa_Model_Task_Sequentiality_sequential_tasks_inst8 Job
         inst_13 Task
         inst_3
         inst_16
         inst_23
         inst_20
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_13)
         arr_seq sched ->
       Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4 Job
         inst_13
         inst_20
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_13
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_13 Task
               inst_3
               inst_16 FP))
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_13)
         sched ->
       forall DB CSB CRPDB : Prosa_Behavior_Time_duration,
       Prosa_Model_Processor_OverheadResourceModel_overhead_resource_model Job
         inst_13 sched DB CSB CRPDB ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Ovh_Fp_FullyNonpreemptive_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts tsk FP DB CSB
         CRPDB L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Ovh_Fp_FullyNonpreemptive_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts tsk FP DB CSB
         CRPDB L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8 Task
         inst_3 Job
         inst_13
         inst_23
         inst_20
         inst_16
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_13)
         arr_seq sched tsk R
```
