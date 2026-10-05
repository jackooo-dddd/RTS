# `get_horizon_of_task`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.get_horizon_of_task`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task`
- Certificate: `get_horizon_of_task_correspondence`

## Official Rocq

```coq
get_horizon_of_task : Equality.sort Task -> duration

get_horizon_of_task is not universe polymorphic
Arguments get_horizon_of_task tsk
get_horizon_of_task is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.get_horizon_of_task
Declared in library prosa.implementation.refinements.arrival_curve, line 11, characters 11-30
get_horizon_of_task
     : Equality.sort Task -> duration
```

Body:

```coq
get_horizon_of_task =
fun tsk : Equality.sort Task => horizon_of (get_arrival_curve_prefix tsk)
     : Equality.sort Task -> duration

Arguments get_horizon_of_task tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Behavior.Time.duration :=
fun tsk =>
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of
    (Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task@{} =
fun tsk : Prosa_Implementation_Refinements_Task_Task =>
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of
  (Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix tsk)
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration

Arguments Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk
```
