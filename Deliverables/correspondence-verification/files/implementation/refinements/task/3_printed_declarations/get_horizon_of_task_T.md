# `get_horizon_of_task_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.get_horizon_of_task_T`
- Lean: `Prosa.Implementation.Refinements.Task.get_horizon_of_task_T`
- Certificate: `get_horizon_of_task_T_correspondence`

## Official Rocq

```coq
get_horizon_of_task_T : forall {T : Type}, one_of T -> @task_T T -> T

get_horizon_of_task_T is not universe polymorphic
Arguments get_horizon_of_task_T {T}%_type_scope {one_of0} tsk
get_horizon_of_task_T is transparent
Expands to: Constant prosa.implementation.refinements.task.get_horizon_of_task_T
Declared in library prosa.implementation.refinements.task, line 80, characters 13-34
@get_horizon_of_task_T
     : forall T : Type, one_of T -> @task_T T -> T
```

Body:

```coq
get_horizon_of_task_T =
fun (T : Type) (one_of0 : one_of T) (tsk : @task_T T) =>
@horizon_of_T T (@get_extrapolated_arrival_curve_T T one_of0 tsk)
     : forall {T : Type}, one_of T -> @task_T T -> T

Arguments get_horizon_of_task_T {T}%_type_scope {one_of0} tsk
```

## Lean

```lean
@Prosa.Implementation.Refinements.Task.get_horizon_of_task_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] → Prosa.Implementation.Refinements.Task.task_T T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.get_horizon_of_task_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] → Prosa.Implementation.Refinements.Task.task_T T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.one_of T] tsk =>
  Prosa.Implementation.Refinements.ArrivalBound.horizon_of_T
    (Prosa.Implementation.Refinements.Task.get_extrapolated_arrival_curve_T tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_get_horizon_of_task_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_Task_get_horizon_of_task_T@{} =
fun (T : Type)
  (inst_3 : Prosa_Implementation_Refinements_Refinements_one_of
                                                                                T)
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) =>
Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T T
  (Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T T
     inst_3 tsk)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> T

Arguments Prosa_Implementation_Refinements_Task_get_horizon_of_task_T T%_type_scope
  inst_3 tsk
```
