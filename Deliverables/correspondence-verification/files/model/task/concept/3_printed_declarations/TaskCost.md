# `TaskCost`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.concept.TaskCost`
- Lean: `Prosa.Model.Task.Concept.TaskCost`
- Certificate: ``

## Official Rocq

```coq
TaskCost : TaskType -> Type

TaskCost is not universe polymorphic
Arguments TaskCost Task
TaskCost is transparent
Expands to: Constant prosa.model.task.concept.TaskCost
Declared in library prosa.model.task.concept, line 27, characters 0-65
TaskCost
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Concept.TaskCost : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_TaskCost
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
