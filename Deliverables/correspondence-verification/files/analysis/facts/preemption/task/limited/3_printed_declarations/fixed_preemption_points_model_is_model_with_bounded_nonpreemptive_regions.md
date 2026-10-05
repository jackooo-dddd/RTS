# `fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.task.limited.fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions`
- Lean: `Prosa.Analysis.Facts.Preemption.Task.Limited.fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions`
- Certificate: `fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions_correspondence`

## Official Rocq

```coq
fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H2 : JobCost Job} {H3 : JobPreemptionPoints Job} {H4 : TaskPreemptionPoints Task}
  (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)),
@valid_fixed_preemption_points_model Task H H4 Job H0 H2 H3 arr_seq ts ->
@model_with_bounded_nonpreemptive_segments Task Job H0 H2
  (@TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task H4)
  (@limited_preemptive_job_model Job H3) arr_seq

fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions is not universe polymorphic
Arguments fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions 
  {Task H Job H0 H2 H3 H4} arr_seq ts%seq_scope H_valid_fixed_preemption_points_model 
  j _
fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.task.limited.fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
Declared in library prosa.analysis.facts.preemption.task.limited, line 52, characters 8-81
@fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H2 : JobCost Job) (H3 : JobPreemptionPoints Job) (H4 : TaskPreemptionPoints Task)
         (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)),
       @valid_fixed_preemption_points_model Task H H4 Job H0 H2 H3 arr_seq ts ->
       @model_with_bounded_nonpreemptive_segments Task Job H0 H2
         (@TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion Task H4)
         (@limited_preemptive_job_model Job H3) arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Task.Limited.fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  [inst_5 : Prosa.Model.Preemption.LimitedPreemptive.JobPreemptionPoints Job]
  [inst_6 : Prosa.Model.Task.Preemption.Parameters.TaskPreemptionPoints Task]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Preemption.LimitedPreemptive.valid_fixed_preemption_points_model arr_seq ts →
    Prosa.Model.Task.Preemption.Parameters.model_with_bounded_nonpreemptive_segments arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Task_Limited_fixed_preemption_points_model_is_model_with_bounded_nonpreemptive_regions
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : 
          DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_7)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_20 : 
          Prosa_Model_Preemption_LimitedPreemptive_JobPreemptionPoints Job
            inst_3)
         (inst_23 : 
          Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints Task
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (ts : Prosa_Model_Task_Concept_TaskSet Task),
       Prosa_Model_Task_Preemption_LimitedPreemptive_valid_fixed_preemption_points_model Task
         inst_7
         inst_10
         inst_23 Job
         inst_3
         inst_13
         inst_17
         inst_20 arr_seq ts ->
       Prosa_Model_Task_Preemption_Parameters_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_13
         inst_17
         (Prosa_Model_Task_Preemption_Parameters_TaskPreemptionPoints_to_TaskMaxNonpreemptiveSegment_conversion
            Task inst_7
            inst_23)
         (Prosa_Model_Preemption_LimitedPreemptive_limited_preemptive_job_model Job
            inst_3
            inst_20)
         arr_seq
```
