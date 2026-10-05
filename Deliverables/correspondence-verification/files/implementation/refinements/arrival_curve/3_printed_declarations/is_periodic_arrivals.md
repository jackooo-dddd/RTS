# `is_periodic_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.is_periodic_arrivals`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.is_periodic_arrivals`
- Certificate: `is_periodic_arrivals_correspondence`

## Official Rocq

```coq
is_periodic_arrivals : Equality.sort Task -> Prop

is_periodic_arrivals is not universe polymorphic
Arguments is_periodic_arrivals tsk
is_periodic_arrivals is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.is_periodic_arrivals
Declared in library prosa.implementation.refinements.arrival_curve, line 42, characters 11-31
is_periodic_arrivals
     : Equality.sort Task -> Prop
```

Body:

```coq
is_periodic_arrivals =
fun tsk : Equality.sort Task => exists p : nat, task_arrival tsk = Periodic p
     : Equality.sort Task -> Prop

Arguments is_periodic_arrivals tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.is_periodic_arrivals : Prosa.Implementation.Refinements.Task.Task → Prop
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.is_periodic_arrivals : Prosa.Implementation.Refinements.Task.Task →
  Prop :=
fun tsk => ∃ p, tsk.task_arrival = Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Periodic p
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_is_periodic_arrivals
     : Prosa_Implementation_Refinements_Task_Task -> SProp
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_is_periodic_arrivals@{} =
fun tsk : Prosa_Implementation_Refinements_Task_Task =>
Exists Nat
  (fun p : Nat =>
   Prosa_Implementation_Definitions_Task_concrete_task_task_arrival tsk =
   Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic p)
     : Prosa_Implementation_Refinements_Task_Task -> SProp

Arguments Prosa_Implementation_Refinements_ArrivalCurve_is_periodic_arrivals tsk
```
