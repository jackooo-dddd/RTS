# `MaxRequestBound`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.arrival.request_bound_functions.MaxRequestBound`
- Lean: `Prosa.Model.Task.Arrival.RequestBoundFunctions.MaxRequestBound`
- Certificate: `MaxRequestBound_source_total, MaxRequestBound_target_total`

## Official Rocq

```coq
MaxRequestBound : TaskType -> Type

MaxRequestBound is not universe polymorphic
Arguments MaxRequestBound Task
MaxRequestBound is transparent
Expands to: Constant prosa.model.task.arrival.request_bound_functions.MaxRequestBound
Declared in library prosa.model.task.arrival.request_bound_functions, line 21, characters 0-88
MaxRequestBound
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Arrival.RequestBoundFunctions.MaxRequestBound : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_MaxRequestBound
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
