# `floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.preemption.task.floating.floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions`
- Lean: `Prosa.Analysis.Facts.Preemption.Task.Floating.floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions`
- Certificate: `floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions_correspondence`

## Official Rocq

```coq
floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H2 : JobCost Job}
  {H3 : TaskMaxNonpreemptiveSegment Task} {H4 : JobPreemptionPoints Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState),
@schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H4) arr_seq sched ->
@valid_model_with_floating_nonpreemptive_regions Task H3 Job H0 H2 H4 arr_seq ->
@valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3 (@limited_preemptive_job_model Job H4)
  PState arr_seq sched

floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions is not universe polymorphic
Arguments floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
  {Task Job H0 H2 H3 H4} arr_seq {PState} sched H_preemption_aware_schedule
  H_valid_model_with_floating_nonpreemptive_regions
floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.task.floating.floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
Declared in library prosa.analysis.facts.preemption.task.floating, line 99, characters 12-94
@floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H2 : JobCost Job)
         (H3 : TaskMaxNonpreemptiveSegment Task) (H4 : JobPreemptionPoints Job)
         (arr_seq : arrival_sequence Job) (PState : ProcessorState Job) (sched : @schedule Job PState),
       @schedule_respects_preemption_model Job PState (@limited_preemptive_job_model Job H4) arr_seq sched ->
       @valid_model_with_floating_nonpreemptive_regions Task H3 Job H0 H2 H4 arr_seq ->
       @valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3
         (@limited_preemptive_job_model Job H4) PState arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Task.Floating.floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobCost Job]
  [inst_4 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_5 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq sched →
    Prosa.Model.Task.Preemption.FloatingNonpreemptive.valid_model_with_floating_nonpreemptive_regions arr_seq →
      Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Task_Floating_floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : 
          DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_17 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_7)
         (inst_20 : 
          Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model Job
         inst_3 PState
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_3
            inst_20)
         arr_seq sched ->
       Prosa_Model_Task_Preemption_FloatingNonpreemptive_valid_model_with_floating_nonpreemptive_regions Task
         inst_7
         inst_17 Job
         inst_3
         inst_10
         inst_14
         inst_20 arr_seq ->
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_10
         inst_14
         inst_17
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_3
            inst_20)
         PState arr_seq sched
```
