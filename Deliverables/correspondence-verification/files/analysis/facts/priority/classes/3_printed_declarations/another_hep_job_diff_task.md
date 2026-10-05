# `another_hep_job_diff_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.another_hep_job_diff_task`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.another_hep_job_diff_task`
- Certificate: `another_hep_job_diff_task_correspondence`

## Official Rocq

```coq
another_hep_job_diff_task :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JLFP_policy Job}
  (j j' : Equality.sort Job),
is_true (~~ @same_task Job Task H j j') -> @another_hep_job Job H0 j j' = @hep_job Job H0 j j'

another_hep_job_diff_task is not universe polymorphic
Arguments another_hep_job_diff_task {Task Job H H0} j j' _
another_hep_job_diff_task is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.another_hep_job_diff_task
Declared in library prosa.analysis.facts.priority.classes, line 26, characters 8-33
@another_hep_job_diff_task
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JLFP_policy Job)
         (j j' : Equality.sort Job),
       is_true (~~ @same_task Job Task H j j') -> @another_hep_job Job H0 j j' = @hep_job Job H0 j j'
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.another_hep_job_diff_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Model.Priority.Definitions.JLFP_policy Job]
  (j j' : Job),
  (!Prosa.Model.Task.Concept.same_task j j') = true →
    Prosa.Model.Priority.Definitions.another_hep_job j j' = Prosa.Model.Priority.Definitions.hep_job j j'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_another_hep_job_diff_task
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
         (j j' : Job),
       @eq Bool
         (Bool_not
            (Prosa_Model_Task_Concept_same_task Job
               inst_7 Task
               inst_3
               inst_10 j j'))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_another_hep_job Job
            inst_7
            inst_14 j j')
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_7
            inst_14 j j')
```
