# `jitter_delay_mapping_valid`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.definitions.delay_propagation.jitter_delay_mapping_valid`
- Lean: `Prosa.Analysis.Definitions.DelayPropagation.jitter_delay_mapping_valid`
- Certificate: `jitter_delay_mapping_valid_correspondence`

## Official Rocq

```coq
jitter_delay_mapping_valid :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {original_arrival : JobArrival Job}
  {H1 : TaskJitter Task} {H2 : JobJitter Job} (ts : TaskSet (Equality.sort Task)),
@valid_jitter_bounds Task H1 Job H0 H2 ts ->
@valid_delay_propagation_mapping Task Task Job Job H0 H0 original_arrival
  (@release_as_arrival Job original_arrival H2) id id (@task_jitter Task H1) ts

jitter_delay_mapping_valid is not universe polymorphic
Arguments jitter_delay_mapping_valid {Task Job H0 original_arrival H1 H2} ts _
jitter_delay_mapping_valid is opaque
Expands to: Constant prosa.analysis.definitions.delay_propagation.jitter_delay_mapping_valid
Declared in library prosa.analysis.definitions.delay_propagation, line 172, characters 9-35
@jitter_delay_mapping_valid
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (original_arrival : JobArrival Job)
         (H1 : TaskJitter Task) (H2 : JobJitter Job) (ts : TaskSet (Equality.sort Task)),
       @valid_jitter_bounds Task H1 Job H0 H2 ts ->
       @valid_delay_propagation_mapping Task Task Job Job H0 H0 original_arrival
         (@release_as_arrival Job original_arrival H2) id id (@task_jitter Task H1) ts
```

## Lean

```lean
@Prosa.Analysis.Definitions.DelayPropagation.jitter_delay_mapping_valid : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (original_arrival : Prosa.Behavior.Job.JobArrival Job)
  [inst_3 : Prosa.Model.Task.Jitter.TaskJitter Task] [inst_4 : Prosa.Model.Readiness.Jitter.JobJitter Job]
  (ts : Prosa.Model.Task.Concept.TaskSet Task),
  Prosa.Model.Task.Jitter.valid_jitter_bounds ts →
    Prosa.Analysis.Definitions.DelayPropagation.valid_delay_propagation_mapping original_arrival
      { job_arrival := fun j => Prosa.Behavior.Job.job_arrival j + Prosa.Model.Readiness.Jitter.job_jitter j } id id
      Prosa.Model.Task.Jitter.task_jitter ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_DelayPropagation_jitter_delay_mapping_valid
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (original_arrival : Prosa_Behavior_Job_JobArrival Job
                               inst_7)
         (inst_16 : 
          Prosa_Model_Task_Jitter_TaskJitter Task
            inst_3)
         (inst_19 : 
          Prosa_Model_Readiness_Jitter_JobJitter Job
            inst_7)
         (ts : Prosa_Model_Task_Concept_TaskSet Task),
       Prosa_Model_Task_Jitter_valid_jitter_bounds Task
         inst_3
         inst_16 Job
         inst_7
         inst_10
         inst_19 ts ->
       Prosa_Analysis_Definitions_DelayPropagation_valid_delay_propagation_mapping Task Task
         inst_3
         inst_3 Job Job
         inst_7
         inst_7
         inst_10
         inst_10 original_arrival
         (Prosa_Behavior_Job_JobArrival_mk Job
            inst_7
            (fun j : Job =>
             HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7
                  original_arrival j)
               (Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job
                  inst_7
                  inst_19 j)))
         (id Job) (id Task)
         (Prosa_Model_Task_Jitter_TaskJitter_task_jitter Task
            inst_3
            inst_16)
         ts
```
