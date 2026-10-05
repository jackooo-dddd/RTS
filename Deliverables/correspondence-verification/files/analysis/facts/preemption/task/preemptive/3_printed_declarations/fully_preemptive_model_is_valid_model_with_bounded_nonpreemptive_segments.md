# `fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments`
- Lean: `Prosa.Analysis.Facts.Preemption.Task.Preemptive.fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments`
- Certificate: `fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments_correspondence`

## Official Rocq

```coq
fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H2 : JobCost Job}
  {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 (@fully_preemptive_task_model Task)
  (@fully_preemptive_job_model Job) PState arr_seq sched

fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments is not universe polymorphic
Arguments fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments 
  {Task Job H0 H2 PState} arr_seq sched
fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments
Declared in library prosa.analysis.facts.preemption.task.preemptive, line 52, characters 12-85
@fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H2 : JobCost Job)
         (PState : ProcessorState Job) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 (@fully_preemptive_task_model Task)
         (@fully_preemptive_job_model Job) PState arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Task.Preemptive.fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Task_Preemptive_fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7
                    PState),
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_3 Job
         inst_7
         inst_10
         inst_14
         (Prosa_Model_Task_Preemption_FullyPreemptive_fully_preemptive_task_model Task
            inst_3)
         (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job
            inst_7)
         PState arr_seq sched
```
