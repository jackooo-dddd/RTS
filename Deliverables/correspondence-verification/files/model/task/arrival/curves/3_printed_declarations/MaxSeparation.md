# `MaxSeparation`

- Kind (Rocq): Class
- Rocq: `prosa.model.task.arrival.curves.MaxSeparation`
- Lean: `Prosa.Model.Task.Arrival.Curves.MaxSeparation`
- Certificate: `MaxSeparation_source_total, MaxSeparation_target_total`

## Official Rocq

```coq
MaxSeparation : TaskType -> Type

MaxSeparation is not universe polymorphic
Arguments MaxSeparation Task
MaxSeparation is transparent
Expands to: Constant prosa.model.task.arrival.curves.MaxSeparation
Declared in library prosa.model.task.arrival.curves, line 36, characters 0-82
MaxSeparation
     : TaskType -> Type
```

## Lean

```lean
Prosa.Model.Task.Arrival.Curves.MaxSeparation : (Task : Prosa.Model.Task.Concept.TaskType) →
  [DecidableEq Task] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_MaxSeparation
     : forall Task : Prosa_Model_Task_Concept_TaskType, DecidableEq Task -> Type
```
