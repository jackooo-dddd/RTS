# `is_sporadic_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.is_sporadic_arrivals`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.is_sporadic_arrivals`
- Certificate: `is_sporadic_arrivals_correspondence`

## Official Rocq

```coq
is_sporadic_arrivals : Equality.sort Task -> Prop

is_sporadic_arrivals is not universe polymorphic
Arguments is_sporadic_arrivals tsk
is_sporadic_arrivals is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.is_sporadic_arrivals
Declared in library prosa.implementation.refinements.arrival_curve, line 46, characters 11-31
is_sporadic_arrivals
     : Equality.sort Task -> Prop
```

Body:

```coq
is_sporadic_arrivals =
fun tsk : Equality.sort Task => exists m : nat, task_arrival tsk = Sporadic m
     : Equality.sort Task -> Prop

Arguments is_sporadic_arrivals tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.is_sporadic_arrivals : Prosa.Implementation.Refinements.Task.Task → Prop
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.is_sporadic_arrivals : Prosa.Implementation.Refinements.Task.Task →
  Prop :=
fun tsk => ∃ m, tsk.task_arrival = Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Sporadic m
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_is_sporadic_arrivals
     : Prosa_Implementation_Refinements_Task_Task -> SProp
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_is_sporadic_arrivals@{} =
fun tsk : Prosa_Implementation_Refinements_Task_Task =>
Exists Nat
  (fun m : Nat =>
   Prosa_Implementation_Definitions_Task_concrete_task_task_arrival tsk =
   Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic m)
     : Prosa_Implementation_Refinements_Task_Task -> SProp

Arguments Prosa_Implementation_Refinements_ArrivalCurve_is_sporadic_arrivals tsk
```
