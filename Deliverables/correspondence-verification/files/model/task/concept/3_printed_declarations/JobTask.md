# `JobTask`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.concept.JobTask`
- Lean: `Prosa.Model.Task.Concept.JobTask`
- Certificate: ``

## Official Rocq

```coq
JobTask : JobType -> TaskType -> Type

JobTask is not universe polymorphic
Arguments JobTask Job Task
JobTask is transparent
Expands to: Constant prosa.model.task.concept.JobTask
Declared in library prosa.model.task.concept, line 19, characters 0-74
JobTask
     : JobType -> TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Concept.JobTask : (Job : Prosa.Behavior.Job.JobType) →
  [DecidableEq Job] → (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type (max u_1 u_2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_JobTask
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
