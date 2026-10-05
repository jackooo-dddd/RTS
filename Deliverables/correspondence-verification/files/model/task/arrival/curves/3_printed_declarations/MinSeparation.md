# `MinSeparation`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.arrival.curves.MinSeparation`
- Lean: `Prosa.Model.Task.Arrival.Curves.MinSeparation`
- Certificate: `MinSeparation_source_total, MinSeparation_target_total`

## Official Rocq

```coq
MinSeparation : TaskType -> Type

MinSeparation is not universe polymorphic
Arguments MinSeparation Task
MinSeparation is transparent
Expands to: Constant prosa.model.task.arrival.curves.MinSeparation
Declared in library prosa.model.task.arrival.curves, line 32, characters 0-82
MinSeparation
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Arrival.Curves.MinSeparation : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_MinSeparation
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
