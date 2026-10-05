# `fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions`
- Lean: `Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions`
- Certificate: `fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions_correspondence`

## Official Rocq

```coq
fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
@model_with_bounded_nonpreemptive_segments Task Job H0 H2 (@fully_nonpreemptive_task_model Task H)
  (@fully_nonpreemptive_job_model Job H2) arr_seq

fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions is not universe polymorphic
Arguments fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions {Task H Job H0 H2} 
  arr_seq H_valid_job_cost j _
fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.task.nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions
Declared in library prosa.analysis.facts.preemption.task.nonpreemptive, line 48, characters 8-77
@fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H0 H2 arr_seq ->
       @model_with_bounded_nonpreemptive_segments Task Job H0 H2 (@fully_nonpreemptive_task_model Task H)
         (@fully_nonpreemptive_job_model Job H2) arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive.fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    Prosa.Model.Task.Preemption.Parameters.model_with_bounded_nonpreemptive_segments arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Task_Nonpreemptive_fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions
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
                      inst_10),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq ->
       Prosa_Model_Task_Preemption_Parameters_model_with_bounded_nonpreemptive_segments Task
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
         arr_seq
```
