# `MaxArrivals`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.arrival.curves.MaxArrivals`
- Lean: `Prosa.Model.Task.Arrival.Curves.MaxArrivals`
- Certificate: `MaxArrivals_source_total, MaxArrivals_target_total`

## Official Rocq

```coq
MaxArrivals : TaskType -> Type

MaxArrivals is not universe polymorphic
Arguments MaxArrivals Task
MaxArrivals is transparent
Expands to: Constant prosa.model.task.arrival.curves.MaxArrivals
Declared in library prosa.model.task.arrival.curves, line 19, characters 0-78
MaxArrivals
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Arrival.Curves.MaxArrivals : (Task : Prosa.Model.Task.Concept.TaskType) → [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_MaxArrivals
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
