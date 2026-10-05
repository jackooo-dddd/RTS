# `get_time_steps_of_task`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.get_time_steps_of_task`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task`
- Certificate: `get_time_steps_of_task_correspondence`

## Official Rocq

```coq
get_time_steps_of_task : Equality.sort Task -> seq duration

get_time_steps_of_task is not universe polymorphic
Arguments get_time_steps_of_task tsk
get_time_steps_of_task is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.get_time_steps_of_task
Declared in library prosa.implementation.refinements.arrival_curve, line 15, characters 11-33
get_time_steps_of_task
     : Equality.sort Task -> seq duration
```

Body:

```coq
get_time_steps_of_task =
fun tsk : Equality.sort Task => time_steps_of (get_arrival_curve_prefix tsk)
     : Equality.sort Task -> seq duration

Arguments get_time_steps_of_task tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task : Prosa.Implementation.Refinements.Task.Task →
  List Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.get_time_steps_of_task : Prosa.Implementation.Refinements.Task.Task →
  List Prosa.Behavior.Time.duration :=
fun tsk =>
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.time_steps_of
    (Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task
     : Prosa_Implementation_Refinements_Task_Task -> List_inst1 Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task@{} =
fun tsk : Prosa_Implementation_Refinements_Task_Task =>
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of
  (Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix tsk)
     : Prosa_Implementation_Refinements_Task_Task -> List_inst1 Prosa_Behavior_Time_duration

Arguments Prosa_Implementation_Refinements_ArrivalCurve_get_time_steps_of_task tsk
```
