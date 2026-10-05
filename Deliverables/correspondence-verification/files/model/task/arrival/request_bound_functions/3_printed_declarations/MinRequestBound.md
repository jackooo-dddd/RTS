# `MinRequestBound`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.arrival.request_bound_functions.MinRequestBound`
- Lean: `Prosa.Model.Task.Arrival.RequestBoundFunctions.MinRequestBound`
- Certificate: `MinRequestBound_source_total, MinRequestBound_target_total`

## Official Rocq

```coq
MinRequestBound : TaskType -> Type

MinRequestBound is not universe polymorphic
Arguments MinRequestBound Task
MinRequestBound is transparent
Expands to: Constant prosa.model.task.arrival.request_bound_functions.MinRequestBound
Declared in library prosa.model.task.arrival.request_bound_functions, line 26, characters 0-88
MinRequestBound
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Arrival.RequestBoundFunctions.MinRequestBound : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
