# `TaskDeadline`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.concept.TaskDeadline`
- Lean: `Prosa.Model.Task.Concept.TaskDeadline`
- Certificate: ``

## Official Rocq

```coq
TaskDeadline : TaskType -> Type

TaskDeadline is not universe polymorphic
Arguments TaskDeadline Task
TaskDeadline is transparent
Expands to: Constant prosa.model.task.concept.TaskDeadline
Declared in library prosa.model.task.concept, line 23, characters 0-73
TaskDeadline
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Concept.TaskDeadline : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_TaskDeadline
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
