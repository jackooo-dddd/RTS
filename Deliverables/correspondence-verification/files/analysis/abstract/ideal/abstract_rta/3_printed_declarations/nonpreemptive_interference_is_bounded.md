# `nonpreemptive_interference_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.abstract_rta.nonpreemptive_interference_is_bounded`
- Lean: `Prosa.Analysis.Abstract.Ideal.AbstractRta.nonpreemptive_interference_is_bounded`
- Certificate: `nonpreemptive_interference_is_bounded_correspondence`

## Official Rocq

```coq
nonpreemptive_interference_is_bounded :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} 
  {H4 : JobPreemptable Job} {PState : ProcessorState Job},
@ideal_progress_proc_model Job PState ->
@unit_service_proc_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@jobs_must_arrive_to_execute Job H2 PState sched ->
@completed_jobs_dont_execute Job PState sched H3 ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_preemption_model Job H3 H4 PState arr_seq sched ->
@valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
forall {H5 : Interference Job} {H6 : InterferingWorkload Job},
@work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
forall interference_bound_function : duration -> duration -> duration,
@job_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6
  (fun F : duration => fun=> F - @task_rtct Task H0 tsk)
  (@relative_time_to_reach_rtct Task H0 Job H2 H3 PState sched tsk H5 H6 interference_bound_function)

nonpreemptive_interference_is_bounded is not universe polymorphic
Arguments nonpreemptive_interference_is_bounded {Task H H0 Job H1 H2 H3 H4 PState}
  H_ideal_progress_proc_model H_unit_service_proc_model arr_seq sched H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute ts%seq_scope tsk H_tsk_in_ts H_valid_preemption_model
  H_valid_run_to_completion_threshold {H5 H6} H_work_conserving interference_bound_function%function_scope 
  t1 t2 Δ j _ _ _ _ _ X _
nonpreemptive_interference_is_bounded is opaque
Expands to: Constant prosa.analysis.abstract.ideal.abstract_rta.nonpreemptive_interference_is_bounded
Declared in library prosa.analysis.abstract.ideal.abstract_rta, line 116, characters 8-45
@nonpreemptive_interference_is_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job)
         (H4 : JobPreemptable Job) (PState : ProcessorState Job),
       @ideal_progress_proc_model Job PState ->
       @unit_service_proc_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @jobs_must_arrive_to_execute Job H2 PState sched ->
       @completed_jobs_dont_execute Job PState sched H3 ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_preemption_model Job H3 H4 PState arr_seq sched ->
       @valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
       forall (H5 : Interference Job) (H6 : InterferingWorkload Job),
       @work_conserving Job H2 H3 PState arr_seq sched H5 H6 ->
       forall interference_bound_function : duration -> duration -> duration,
       @job_interference_is_bounded_by Job Task H1 H2 H3 PState arr_seq sched tsk H5 H6
         (fun F : duration => fun=> F - @task_rtct Task H0 tsk)
         (@relative_time_to_reach_rtct Task H0 Job H2 H3 PState sched tsk H5 H6 interference_bound_function)
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.AbstractRta.nonpreemptive_interference_is_bounded : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
        (sched : Prosa.Behavior.Schedule.schedule PState),
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
            ∀ (ts : List Task) (tsk : Task),
              decide (tsk ∈ ts) = true →
                Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                  Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
                    ∀ [inst_8 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                      [inst_9 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                      Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                        ∀
                          (interference_bound_function :
                            Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                          Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched tsk
                            (fun F x => F - Prosa.Model.Task.Preemption.Parameters.task_rtct tsk)
                            (Prosa.Analysis.Abstract.AbstractRta.relative_time_to_reach_rtct sched tsk
                              interference_bound_function)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_AbstractRta_nonpreemptive_interference_is_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_13)
         (inst_26 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_13)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_13),
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_13 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_13 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_13 PState),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_13
         inst_20 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_13 PState sched
         inst_23 ->
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
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_13
         inst_23
         inst_26 PState arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_23
         inst_26
         inst_9 arr_seq tsk ->
       forall
         (inst_77 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_13)
         (inst_80 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_13),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_13
         inst_77
         inst_80
         inst_20
         inst_23 PState arr_seq sched ->
       forall
         interference_bound_function : Prosa_Behavior_Time_duration ->
                                       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job
         inst_13
         inst_77
         inst_80
         inst_20
         inst_23 PState arr_seq sched
         Task inst_3
         inst_16 tsk
         (fun F _ : Prosa_Behavior_Time_duration =>
          HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work Prosa_Behavior_Time_duration
            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) F
            (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
               inst_3
               inst_9 tsk))
         (Prosa_Analysis_Abstract_AbstractRta_relative_time_to_reach_rtct Task
            inst_3
            inst_9 Job
            inst_13
            inst_20
            inst_23 PState sched tsk
            inst_77
            inst_80
            interference_bound_function)
```
