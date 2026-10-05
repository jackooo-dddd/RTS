# `get_arrival_curve_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.task.get_arrival_curve_prefix`
- Lean: `Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix`
- Certificate: `get_arrival_curve_prefix_correspondence`

## Official Rocq

```coq
get_arrival_curve_prefix : concrete_task -> ArrivalCurvePrefix

get_arrival_curve_prefix is not universe polymorphic
Arguments get_arrival_curve_prefix tsk
get_arrival_curve_prefix is transparent
Expands to: Constant prosa.implementation.definitions.task.get_arrival_curve_prefix
Declared in library prosa.implementation.definitions.task, line 77, characters 11-35
get_arrival_curve_prefix
     : concrete_task -> ArrivalCurvePrefix
```

Body:

```coq
get_arrival_curve_prefix =
fun tsk : concrete_task =>
match task_arrival tsk with
| @Periodic p => inter_arrival_to_prefix p
| @Sporadic m => inter_arrival_to_prefix m
| @ArrivalPrefix steps => steps
end
     : concrete_task -> ArrivalCurvePrefix

Arguments get_arrival_curve_prefix tsk
```

## Lean

```lean
Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix : Prosa.Implementation.Definitions.Task.concrete_task →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix
```

Body:

```lean
def Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix : Prosa.Implementation.Definitions.Task.concrete_task →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix :=
fun tsk =>
  match tsk.task_arrival with
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Periodic p =>
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.inter_arrival_to_prefix p
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Sporadic m =>
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.inter_arrival_to_prefix m
  | Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.ArrivalPrefix steps => steps
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix
     : Prosa_Implementation_Definitions_Task_concrete_task ->
       Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix
```

Body:

```coq
Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix@{} =
fun tsk : Prosa_Implementation_Definitions_Task_concrete_task =>
Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix_match_1
  (fun _ : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound =>
   Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix)
  (Prosa_Implementation_Definitions_Task_concrete_task_task_arrival tsk)
  (fun p : Nat => Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_inter_arrival_to_prefix p)
  (fun p : Nat => Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_inter_arrival_to_prefix p)
  (fun steps : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix => steps)
     : Prosa_Implementation_Definitions_Task_concrete_task ->
       Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix

Arguments Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix tsk
```
