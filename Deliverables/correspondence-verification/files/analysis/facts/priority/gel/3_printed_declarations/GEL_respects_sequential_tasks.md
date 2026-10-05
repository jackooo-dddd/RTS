# `GEL_respects_sequential_tasks`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.gel.GEL_respects_sequential_tasks`
- Lean: `Prosa.Analysis.Facts.Priority.Gel.GEL_respects_sequential_tasks`
- Certificate: `GEL_respects_sequential_tasks_correspondence`

## Official Rocq

```coq
GEL_respects_sequential_tasks :
forall {Task : concept.TaskType} {Job : job.JobType} {H : concept.JobTask Job Task}
  {H0 : gel.PriorityPoint Task} {Arrival : job.JobArrival Job},
@definitions.policy_respects_sequential_tasks Task Job H Arrival (@gel.GEL Job Task H0 Arrival H)

GEL_respects_sequential_tasks is not universe polymorphic
Arguments GEL_respects_sequential_tasks {Task Job H H0 Arrival} j1 j2 _ _
GEL_respects_sequential_tasks is opaque
Expands to: Constant prosa.analysis.facts.priority.gel.GEL_respects_sequential_tasks
Declared in library prosa.analysis.facts.priority.gel, line 62, characters 8-37
@GEL_respects_sequential_tasks
     : forall (Task : concept.TaskType) (Job : job.JobType) (H : concept.JobTask Job Task)
         (H0 : gel.PriorityPoint Task) (Arrival : job.JobArrival Job),
       @definitions.policy_respects_sequential_tasks Task Job H Arrival (@gel.GEL Job Task H0 Arrival H)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Gel.GEL_respects_sequential_tasks : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  [Arrival : Prosa.Behavior.Job.JobArrival Job],
  Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks (Prosa.Model.Priority.Gel.GEL Job Task)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Gel_GEL_respects_sequential_tasks
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (Arrival : Prosa_Behavior_Job_JobArrival Job
                      inst_7),
       Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks Task
         inst_3 Job
         inst_7
         inst_10 Arrival
         (Prosa_Model_Priority_Gel_GEL Job
            inst_7 Task
            inst_3
            inst_14 Arrival
            inst_10)
```
