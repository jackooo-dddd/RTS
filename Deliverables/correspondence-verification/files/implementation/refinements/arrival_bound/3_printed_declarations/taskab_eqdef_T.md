# `taskab_eqdef_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.taskab_eqdef_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.taskab_eqdef_T`
- Certificate: `taskab_eqdef_T_correspondence`

## Official Rocq

```coq
taskab_eqdef_T :
forall {T : Type},
eq_of T -> eq_of (T * seq (T * T)) -> @task_arrivals_bound_T T -> @task_arrivals_bound_T T -> bool

taskab_eqdef_T is not universe polymorphic
Arguments taskab_eqdef_T {T}%_type_scope {eq_of0 eq_of2} tb1 tb2
taskab_eqdef_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.taskab_eqdef_T
Declared in library prosa.implementation.refinements.arrival_bound, line 34, characters 13-27
@taskab_eqdef_T
     : forall T : Type,
       eq_of T -> eq_of (T * seq (T * T)) -> @task_arrivals_bound_T T -> @task_arrivals_bound_T T -> bool
```

Body:

```coq
taskab_eqdef_T =
fun (T : Type) (eq_of0 : eq_of T) (eq_of2 : eq_of (T * seq (T * T))) (tb1 tb2 : @task_arrivals_bound_T T) =>
match tb1 with
| @Periodic_T _ p1 => match tb2 with
                      | @Periodic_T _ p2 => (p1 == p2)%C
                      | _ => false
                      end
| @Sporadic_T _ s1 => match tb2 with
                      | @Sporadic_T _ s2 => (s1 == s2)%C
                      | _ => false
                      end
| @ArrivalPrefix_T _ s1 => match tb2 with
                           | @ArrivalPrefix_T _ s2 => (s1 == s2)%C
                           | _ => false
                           end
end
     : forall {T : Type},
       eq_of T -> eq_of (T * seq (T * T)) -> @task_arrivals_bound_T T -> @task_arrivals_bound_T T -> bool

Arguments taskab_eqdef_T {T}%_type_scope {eq_of0 eq_of2} tb1 tb2
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.taskab_eqdef_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.eq_of T] →
    [Prosa.Implementation.Refinements.Refinements.eq_of (T × List (T × T))] →
      Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T →
        Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.taskab_eqdef_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.eq_of T] →
    [Prosa.Implementation.Refinements.Refinements.eq_of (T × List (T × T))] →
      Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T →
        Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T T → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.eq_of T]
    [Prosa.Implementation.Refinements.Refinements.eq_of (T × List (T × T))] tb1 tb2 =>
  match tb1, tb2 with
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Periodic_T p1,
    Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Periodic_T p2 =>
    Prosa.Implementation.Refinements.Refinements.eq_op p1 p2
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Sporadic_T s1,
    Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Sporadic_T s2 =>
    Prosa.Implementation.Refinements.Refinements.eq_op s1 s2
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.ArrivalPrefix_T s1,
    Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.ArrivalPrefix_T s2 =>
    Prosa.Implementation.Refinements.Refinements.eq_op s1 s2
  | x, x_1 => false
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_taskab_eqdef_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of (Prod_inst3 T (List_inst1 (Prod_inst3 T T))) ->
       Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T ->
       Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_taskab_eqdef_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_eq_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_eq_of (Prod_inst3 T (List_inst1 (Prod_inst3 T T))))
  (tb1 tb2 : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T) =>
Prosa_Implementation_Refinements_ArrivalBound_taskab_eqdef_T_match_1 T
  (fun _ _ : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T => Bool) tb1 tb2
  (fun p1 p2 : T =>
   Prosa_Implementation_Refinements_Refinements_eq_of_eq_op T
     inst_3 p1 p2)
  (fun p1 p2 : T =>
   Prosa_Implementation_Refinements_Refinements_eq_of_eq_op T
     inst_3 p1 p2)
  (fun s1 s2 : Prod_inst3 T (List_inst1 (Prod_inst3 T T)) =>
   Prosa_Implementation_Refinements_Refinements_eq_of_eq_op (Prod_inst3 T (List_inst1 (Prod_inst3 T T)))
     inst_6 s1 s2)
  (fun _ _ : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T => Bool_false)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of (Prod_inst3 T (List_inst1 (Prod_inst3 T T))) ->
       Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T ->
       Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalBound_taskab_eqdef_T T%_type_scope
  inst_3
  inst_6 
  tb1 tb2
```
