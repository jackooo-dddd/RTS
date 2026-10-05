# `concrete_max_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.task.concrete_max_arrivals`
- Lean: `Prosa.Implementation.Definitions.Task.concrete_max_arrivals`
- Certificate: `concrete_max_arrivals_correspondence`

## Official Rocq

```coq
concrete_max_arrivals : concrete_task -> duration -> nat

concrete_max_arrivals is not universe polymorphic
Arguments concrete_max_arrivals tsk Δ
concrete_max_arrivals is transparent
Expands to: Constant prosa.implementation.definitions.task.concrete_max_arrivals
Declared in library prosa.implementation.definitions.task, line 85, characters 11-32
concrete_max_arrivals
     : concrete_task -> duration -> nat
```

Body:

```coq
concrete_max_arrivals =
fun tsk : concrete_task => [eta extrapolated_arrival_curve (get_arrival_curve_prefix tsk)]
     : concrete_task -> duration -> nat

Arguments concrete_max_arrivals tsk Δ
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.concrete_max_arrivals : Prosa.Implementation.Definitions.Task.concrete_task →
  Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Implementation.Definitions.Task.concrete_max_arrivals : Prosa.Implementation.Definitions.Task.concrete_task →
  Prosa.Behavior.Time.duration → ℕ :=
fun tsk Δ =>
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve
    (Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix tsk) Δ
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_concrete_max_arrivals
     : Prosa_Implementation_Definitions_Task_concrete_task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Implementation_Definitions_Task_concrete_max_arrivals@{} =
fun (tsk : Prosa_Implementation_Definitions_Task_concrete_task) (_UU0394_ : Prosa_Behavior_Time_duration) =>
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve
  (Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix tsk) _UU0394_
     : Prosa_Implementation_Definitions_Task_concrete_task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Implementation_Definitions_Task_concrete_max_arrivals tsk a____at____internal__hyg0
```
