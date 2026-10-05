# `another_task_hep_job_taskwise_antireflexive`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.classes.another_task_hep_job_taskwise_antireflexive`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.another_task_hep_job_taskwise_antireflexive`
- Certificate: `another_task_hep_job_taskwise_antireflexive_correspondence`

## Official Rocq

```coq
another_task_hep_job_taskwise_antireflexive :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JLFP_policy Job}
  (tsk : Equality.sort Task) (j j' : Equality.sort Job),
is_true (@job_of_task Job Task H tsk j) ->
is_true (@job_of_task Job Task H tsk j') -> ~ is_true (@another_task_hep_job Task Job H H0 j' j)

another_task_hep_job_taskwise_antireflexive is not universe polymorphic
Arguments another_task_hep_job_taskwise_antireflexive {Task Job H H0} tsk j j' _ _ _
another_task_hep_job_taskwise_antireflexive is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.another_task_hep_job_taskwise_antireflexive
Declared in library prosa.analysis.facts.priority.classes, line 40, characters 8-51
@another_task_hep_job_taskwise_antireflexive
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JLFP_policy Job)
         (tsk : Equality.sort Task) (j j' : Equality.sort Job),
       is_true (@job_of_task Job Task H tsk j) ->
       is_true (@job_of_task Job Task H tsk j') -> ~ is_true (@another_task_hep_job Task Job H H0 j' j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.another_task_hep_job_taskwise_antireflexive : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Model.Priority.Definitions.JLFP_policy Job] (tsk : Task) (j j' : Job),
  Prosa.Model.Task.Concept.job_of_task tsk j = true →
    Prosa.Model.Task.Concept.job_of_task tsk j' = true →
      ¬Prosa.Model.Priority.Definitions.another_task_hep_job j' j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_another_task_hep_job_taskwise_antireflexive
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
         (tsk : Task) (j j' : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j')
         Bool_true ->
       Not
         (@eq Bool
            (Prosa_Model_Priority_Definitions_another_task_hep_job Task
               inst_3 Job
               inst_7
               inst_10
               inst_14 j' j)
            Bool_true)
```
