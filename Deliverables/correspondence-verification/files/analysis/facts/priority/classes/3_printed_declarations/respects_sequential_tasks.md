# `respects_sequential_tasks`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.facts.priority.classes.respects_sequential_tasks`
- Lean: `Prosa.Analysis.Facts.Priority.Classes.respects_sequential_tasks`
- Certificate: `respects_sequential_tasks_correspondence`

## Official Rocq

```coq
respects_sequential_tasks :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@policy_respects_sequential_tasks Task Job H0 H1 (@FP_to_JLFP Job Task H0 FP)

respects_sequential_tasks is not universe polymorphic
Arguments respects_sequential_tasks {Task Job H0 H1 FP} _ j1 j2 _ _
respects_sequential_tasks is opaque
Expands to: Constant prosa.analysis.facts.priority.classes.respects_sequential_tasks
Declared in library prosa.analysis.facts.priority.classes, line 259, characters 9-34
@respects_sequential_tasks
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (FP : FP_policy Task),
       @reflexive_task_priorities Task FP ->
       @policy_respects_sequential_tasks Task Job H0 H1 (@FP_to_JLFP Job Task H0 FP)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Classes.respects_sequential_tasks : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
  Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
    Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks (Prosa.Model.Priority.Coercion.FP_to_JLFP FP)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Classes_respects_sequential_tasks
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks Task
         inst_3 Job
         inst_7
         inst_10
         inst_14
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_7 Task
            inst_3
            inst_10 FP)
```
