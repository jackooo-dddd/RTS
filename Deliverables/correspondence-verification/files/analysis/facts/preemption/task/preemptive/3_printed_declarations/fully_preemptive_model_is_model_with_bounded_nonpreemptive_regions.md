# `fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions`
- Lean: `Prosa.Analysis.Facts.Preemption.Task.Preemptive.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions`
- Certificate: `fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions_correspondence`

## Official Rocq

```coq
fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H2 : JobCost Job}
  (arr_seq : arrival_sequence Job),
@model_with_bounded_nonpreemptive_segments Task Job H0 H2 (@fully_preemptive_task_model Task)
  (@fully_preemptive_job_model Job) arr_seq

fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions is not universe polymorphic
Arguments fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions {Task Job H0 H2} arr_seq j _
fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.task.preemptive.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions
Declared in library prosa.analysis.facts.preemption.task.preemptive, line 38, characters 8-74
@fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H2 : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @model_with_bounded_nonpreemptive_segments Task Job H0 H2 (@fully_preemptive_task_model Task)
         (@fully_preemptive_job_model Job) arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Task.Preemptive.fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Preemption.Parameters.model_with_bounded_nonpreemptive_segments arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Task_Preemptive_fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Model_Task_Preemption_Parameters_model_with_bounded_nonpreemptive_segments Task
         inst_3 Job
         inst_7
         inst_10
         inst_14
         (Prosa_Model_Task_Preemption_FullyPreemptive_fully_preemptive_task_model Task
            inst_3)
         (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job
            inst_7)
         arr_seq
```
