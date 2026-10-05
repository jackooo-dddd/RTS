# `fifo_respects_sequential_tasks`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.priority.fifo.fifo_respects_sequential_tasks`
- Lean: `Prosa.Analysis.Facts.Priority.Fifo.fifo_respects_sequential_tasks`
- Certificate: `fifo_respects_sequential_tasks_correspondence`

## Official Rocq

```coq
fifo_respects_sequential_tasks :
forall {Job : JobType} {Arrival : JobArrival Job} {Task : TaskType} {H0 : JobTask Job Task},
@policy_respects_sequential_tasks Task Job H0 Arrival (@FIFO Job Arrival)

fifo_respects_sequential_tasks is not universe polymorphic
Arguments fifo_respects_sequential_tasks {Job Arrival Task H0} j1 j2 _ _
fifo_respects_sequential_tasks is opaque
Expands to: Constant prosa.analysis.facts.priority.fifo.fifo_respects_sequential_tasks
Declared in library prosa.analysis.facts.priority.fifo, line 199, characters 9-39
@fifo_respects_sequential_tasks
     : forall (Job : JobType) (Arrival : JobArrival Job) (Task : TaskType) (H0 : JobTask Job Task),
       @policy_respects_sequential_tasks Task Job H0 Arrival (@FIFO Job Arrival)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Fifo.fifo_respects_sequential_tasks : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_2 : DecidableEq Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task],
  Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks (Prosa.Model.Priority.Fifo.FIFO Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Fifo_fifo_respects_sequential_tasks
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_10 : DecidableEq Task)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_10),
       Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks Task
         inst_10 Job
         inst_3
         inst_13
         inst_6
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_3
            inst_6)
```
