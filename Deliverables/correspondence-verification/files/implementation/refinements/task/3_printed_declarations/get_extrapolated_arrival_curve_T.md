# `get_extrapolated_arrival_curve_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.get_extrapolated_arrival_curve_T`
- Lean: `Prosa.Implementation.Refinements.Task.get_extrapolated_arrival_curve_T`
- Certificate: `get_extrapolated_arrival_curve_T_correspondence`

## Official Rocq

```coq
get_extrapolated_arrival_curve_T : forall {T : Type}, one_of T -> @task_T T -> T * seq (T * T)

get_extrapolated_arrival_curve_T is not universe polymorphic
Arguments get_extrapolated_arrival_curve_T {T}%_type_scope {one_of0} tsk
get_extrapolated_arrival_curve_T is transparent
Expands to: Constant prosa.implementation.refinements.task.get_extrapolated_arrival_curve_T
Declared in library prosa.implementation.refinements.task, line 54, characters 13-45
@get_extrapolated_arrival_curve_T
     : forall T : Type, one_of T -> @task_T T -> T * seq (T * T)
```

Body:

```coq
get_extrapolated_arrival_curve_T =
fun (T : Type) (one_of0 : one_of T) (tsk : @task_T T) =>
match @task_arrival_T T tsk with
| @Periodic_T _ p => @inter_arrival_to_extrapolated_arrival_curve_T T one_of0 p
| @Sporadic_T _ m => @inter_arrival_to_extrapolated_arrival_curve_T T one_of0 m
| @ArrivalPrefix_T _ steps => steps
end
     : forall {T : Type}, one_of T -> @task_T T -> T * seq (T * T)

Arguments get_extrapolated_arrival_curve_T {T}%_type_scope {one_of0} tsk
```

## Lean

```lean
@Prosa.Implementation.Refinements.Task.get_extrapolated_arrival_curve_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    Prosa.Implementation.Refinements.Task.task_T T → T × List (T × T)
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.get_extrapolated_arrival_curve_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    Prosa.Implementation.Refinements.Task.task_T T → T × List (T × T) :=
fun {T} [Prosa.Implementation.Refinements.Refinements.one_of T] tsk =>
  match tsk.task_arrival_T with
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Periodic_T p =>
    Prosa.Implementation.Refinements.Task.inter_arrival_to_extrapolated_arrival_curve_T p
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Sporadic_T m =>
    Prosa.Implementation.Refinements.Task.inter_arrival_to_extrapolated_arrival_curve_T m
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.ArrivalPrefix_T steps => steps
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Prod_inst3 T (List_inst1 (Prod_inst3 T T))
```

Body:

```coq
Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T@{} =
fun (T : Type)
  (inst_3 : Prosa_Implementation_Refinements_Refinements_one_of
                                                                                T)
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) =>
Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T_match_1 T
  (fun _ : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T =>
   Prod_inst3 T (List_inst1 (Prod_inst3 T T)))
  (Prosa_Implementation_Refinements_Task_task_T_task_arrival_T T tsk)
  (fun p : T =>
   Prosa_Implementation_Refinements_Task_inter_arrival_to_extrapolated_arrival_curve_T T
     inst_3 p)
  (fun p : T =>
   Prosa_Implementation_Refinements_Task_inter_arrival_to_extrapolated_arrival_curve_T T
     inst_3 p)
  (fun steps : Prod_inst3 T (List_inst1 (Prod_inst3 T T)) => steps)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Prod_inst3 T (List_inst1 (Prod_inst3 T T))

Arguments Prosa_Implementation_Refinements_Task_get_extrapolated_arrival_curve_T 
  T%_type_scope inst_3 
  tsk
```
