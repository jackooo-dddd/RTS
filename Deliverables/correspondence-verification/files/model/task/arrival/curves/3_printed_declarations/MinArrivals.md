# `MinArrivals`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.arrival.curves.MinArrivals`
- Lean: `Prosa.Model.Task.Arrival.Curves.MinArrivals`
- Certificate: `MinArrivals_source_total, MinArrivals_target_total`

## Official Rocq

```coq
MinArrivals : TaskType -> Type

MinArrivals is not universe polymorphic
Arguments MinArrivals Task
MinArrivals is transparent
Expands to: Constant prosa.model.task.arrival.curves.MinArrivals
Declared in library prosa.model.task.arrival.curves, line 23, characters 0-78
MinArrivals
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Arrival.Curves.MinArrivals : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_MinArrivals
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
