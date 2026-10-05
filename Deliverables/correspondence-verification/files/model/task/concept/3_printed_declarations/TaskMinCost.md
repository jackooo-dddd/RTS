# `TaskMinCost`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.concept.TaskMinCost`
- Lean: `Prosa.Model.Task.Concept.TaskMinCost`
- Certificate: ``

## Official Rocq

```coq
TaskMinCost : TaskType -> Type

TaskMinCost is not universe polymorphic
Arguments TaskMinCost Task
TaskMinCost is transparent
Expands to: Constant prosa.model.task.concept.TaskMinCost
Declared in library prosa.model.task.concept, line 31, characters 0-72
TaskMinCost
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Concept.TaskMinCost : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Concept_TaskMinCost
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
