# `SporadicModel`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.arrival.sporadic.SporadicModel`
- Lean: `Prosa.Model.Task.Arrival.Sporadic.SporadicModel`
- Certificate: `sp_sporadic_model_import_certificate`

## Official Rocq

```coq
SporadicModel : TaskType -> Type

SporadicModel is not universe polymorphic
Arguments SporadicModel Task
SporadicModel is transparent
Expands to: Constant prosa.model.task.arrival.sporadic.SporadicModel
Declared in library prosa.model.task.arrival.sporadic, line 16, characters 0-90
SporadicModel
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Arrival.Sporadic.SporadicModel : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Sporadic_SporadicModel
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
