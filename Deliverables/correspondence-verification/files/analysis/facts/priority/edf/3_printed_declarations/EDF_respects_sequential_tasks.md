# `EDF_respects_sequential_tasks`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.edf.EDF_respects_sequential_tasks`
- Lean: `Prosa.Analysis.Facts.Priority.Edf.EDF_respects_sequential_tasks`
- Certificate: `EDF_respects_sequential_tasks_correspondence`

## Official Rocq

```coq
EDF_respects_sequential_tasks :
forall {Job : JobType} {H : JobArrival Job} {Task : TaskType} {H0 : TaskDeadline Task}
  {H1 : JobTask Job Task},
@policy_respects_sequential_tasks Task Job H1 H
  (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H H1))

EDF_respects_sequential_tasks is not universe polymorphic
Arguments EDF_respects_sequential_tasks {Job H Task H0 H1} j1 j2 _ _
EDF_respects_sequential_tasks is opaque
Expands to: Constant prosa.analysis.facts.priority.edf.EDF_respects_sequential_tasks
Declared in library prosa.analysis.facts.priority.edf, line 56, characters 10-39
@EDF_respects_sequential_tasks
     : forall (Job : JobType) (H : JobArrival Job) (Task : TaskType) (H0 : TaskDeadline Task)
         (H1 : JobTask Job Task),
       @policy_respects_sequential_tasks Task Job H1 H
         (@EDF Job (@job_deadline_from_task_deadline Job Task H0 H H1))
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Edf.EDF_respects_sequential_tasks : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_2 : DecidableEq Task] [inst_3 : Prosa.Model.Task.Concept.TaskDeadline Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task],
  Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks (Prosa.Model.Priority.Edf.EDF Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Edf_EDF_respects_sequential_tasks
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_10 : DecidableEq Task)
         (inst_13 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_10)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_10),
       Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks Task
         inst_10 Job
         inst_3
         inst_16
         inst_6
         (Prosa_Model_Priority_Edf_EDF Job
            inst_3
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_3
               inst_10
               inst_13
               inst_6
               inst_16))
```
