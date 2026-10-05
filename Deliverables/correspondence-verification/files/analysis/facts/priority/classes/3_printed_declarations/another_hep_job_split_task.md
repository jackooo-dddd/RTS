# `another_hep_job_split_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.another_hep_job_split_task`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.another_hep_job_split_task`
- Certificate: `another_hep_job_split_task_correspondence`

## Official Rocq

```coq
another_hep_job_split_task :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JLFP_policy Job}
  (j1 j2 : Equality.sort Job),
@another_hep_job Job H0 j1 j2 =
@another_task_hep_job Task Job H H0 j1 j2 || @another_hep_job_of_same_task Task Job H H0 j1 j2

another_hep_job_split_task is not universe polymorphic
Arguments another_hep_job_split_task {Task Job H H0} j1 j2
another_hep_job_split_task is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.another_hep_job_split_task
Declared in library prosa.analysis.facts.priority.classes, line 62, characters 8-34
@another_hep_job_split_task
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JLFP_policy Job)
         (j1 j2 : Equality.sort Job),
       @another_hep_job Job H0 j1 j2 =
       @another_task_hep_job Task Job H H0 j1 j2 || @another_hep_job_of_same_task Task Job H H0 j1 j2
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.another_hep_job_split_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Model.Priority.Definitions.JLFP_policy Job]
  (j1 j2 : Job),
  Prosa.Model.Priority.Definitions.another_hep_job j1 j2 =
    (Prosa.Model.Priority.Definitions.another_task_hep_job j1 j2 ||
      Prosa.Model.Priority.Definitions.another_hep_job_of_same_task j1 j2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_another_hep_job_split_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_7)
         (j1 j2 : Job),
       @eq Bool
         (Prosa_Model_Priority_Definitions_another_hep_job Job
            inst_7
            inst_14 j1 j2)
         (Bool_or
            (Prosa_Model_Priority_Definitions_another_task_hep_job Task
               inst_3 Job
               inst_7
               inst_10
               inst_14 j1 j2)
            (Prosa_Model_Priority_Definitions_another_hep_job_of_same_task Task
               inst_3 Job
               inst_7
               inst_10
               inst_14 j1 j2))
```
