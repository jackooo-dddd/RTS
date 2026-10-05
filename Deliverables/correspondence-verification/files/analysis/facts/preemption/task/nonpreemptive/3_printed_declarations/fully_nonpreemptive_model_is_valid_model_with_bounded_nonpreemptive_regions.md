# `fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions`
- Lean: `Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions`
- Certificate: `fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions_correspondence`

## Official Rocq

```coq
fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H2 : JobCost Job} (arr_seq : arrival_sequence Job) {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall sched : @schedule Job PState,
@nonpreemptive_schedule Job H2 PState sched ->
@completed_jobs_dont_execute Job PState sched H2 ->
@arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
@valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 (@fully_nonpreemptive_task_model Task H)
  (@fully_nonpreemptive_job_model Job H2) PState arr_seq sched

fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions is not universe polymorphic
Arguments fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions 
  {Task H Job H0 H2} arr_seq {PState} H_unit_service sched H_nonpreemptive_sched
  H_completed_jobs_dont_execute H_valid_job_cost
fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions
Declared in library prosa.analysis.facts.preemption.task.nonpreemptive, line 84, characters 12-87
@fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H2 : JobCost Job) (arr_seq : arrival_sequence Job) (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall sched : @schedule Job PState,
       @nonpreemptive_schedule Job H2 PState sched ->
       @completed_jobs_dont_execute Job PState sched H2 ->
       @arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
       @valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2
         (@fully_nonpreemptive_task_model Task H) (@fully_nonpreemptive_job_model Job H2) PState arr_seq
         sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive.fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule sched →
        Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
          Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
            Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Task_Nonpreemptive_fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_10),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_10 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_10
                   PState,
       Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule Job
         inst_10
         inst_17 PState
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_10 PState
         sched inst_17 ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq ->
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_3 Job
         inst_10
         inst_13
         inst_17
         (Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model Task
            inst_3
            inst_6)
         (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
            inst_10
            inst_17)
         PState arr_seq sched
```
