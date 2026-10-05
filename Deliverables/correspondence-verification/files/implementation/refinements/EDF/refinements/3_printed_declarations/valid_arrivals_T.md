# `valid_arrivals_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.refinements.valid_arrivals_T`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.valid_arrivals_T`
- Certificate: `valid_arrivals_T_correspondence`

## Official Rocq

```coq
valid_arrivals_T :
forall {T : Type}, zero_of T -> one_of T -> eq_of T -> leq_of T -> lt_of T -> @task_T T -> bool

valid_arrivals_T is not universe polymorphic
Arguments valid_arrivals_T {T}%_type_scope {zero_of0 one_of0 eq_of0 leq_of0 lt_of0} tsk
valid_arrivals_T is transparent
Expands to: Constant prosa.implementation.refinements.EDF.refinements.valid_arrivals_T
Declared in library prosa.implementation.refinements.EDF.refinements, line 50, characters 13-29
@valid_arrivals_T
     : forall T : Type, zero_of T -> one_of T -> eq_of T -> leq_of T -> lt_of T -> @task_T T -> bool
```

Body:

```coq
valid_arrivals_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (eq_of0 : eq_of T) (leq_of0 : leq_of T)
  (lt_of0 : lt_of T) (tsk : @task_T T) =>
match @task_arrival_T T tsk with
| @Periodic_T _ p => (1 <= p)%C
| @Sporadic_T _ m => (1 <= m)%C
| @ArrivalPrefix_T _ emax_vec =>
    @valid_extrapolated_arrival_curve_T T zero_of0 one_of0 eq_of0 leq_of0 lt_of0 emax_vec
end
     : forall {T : Type}, zero_of T -> one_of T -> eq_of T -> leq_of T -> lt_of T -> @task_T T -> bool

Arguments valid_arrivals_T {T}%_type_scope {zero_of0 one_of0 eq_of0 leq_of0 lt_of0} tsk
```

## Lean

```lean
@Prosa.Implementation.Refinements.EDF.Refinements.valid_arrivals_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.eq_of T] →
        [Prosa.Implementation.Refinements.Refinements.leq_of T] →
          [Prosa.Implementation.Refinements.Refinements.lt_of T] → Prosa.Implementation.Refinements.Task.task_T T → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.Refinements.valid_arrivals_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.eq_of T] →
        [Prosa.Implementation.Refinements.Refinements.leq_of T] →
          [Prosa.Implementation.Refinements.Refinements.lt_of T] →
            Prosa.Implementation.Refinements.Task.task_T T → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.eq_of T] [Prosa.Implementation.Refinements.Refinements.leq_of T]
    [Prosa.Implementation.Refinements.Refinements.lt_of T] tsk =>
  match tsk.task_arrival_T with
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Periodic_T p =>
    Prosa.Implementation.Refinements.Refinements.leq_op Prosa.Implementation.Refinements.Refinements.one_op p
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Sporadic_T m =>
    Prosa.Implementation.Refinements.Refinements.leq_op Prosa.Implementation.Refinements.Refinements.one_op m
  | Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.ArrivalPrefix_T emax_vec =>
    Prosa.Implementation.Refinements.ArrivalBound.valid_extrapolated_arrival_curve_T emax_vec
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_valid_arrivals_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_Refinements_valid_arrivals_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_one_of T)
  (inst_9 : 
   Prosa_Implementation_Refinements_Refinements_eq_of T)
  (inst_12 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (inst_15 : 
   Prosa_Implementation_Refinements_Refinements_lt_of T)
  (tsk : Prosa_Implementation_Refinements_Task_task_T T) =>
Prosa_Implementation_Refinements_EDF_Refinements_valid_arrivals_T_match_1 T
  (fun _ : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T T => Bool)
  (Prosa_Implementation_Refinements_Task_task_T_task_arrival_T T tsk)
  (fun p : T =>
   Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
     inst_12
     (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
        inst_6)
     p)
  (fun p : T =>
   Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
     inst_12
     (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
        inst_6)
     p)
  (fun ac_prefix_vec : Prod_inst3 T (List_inst1 (Prod_inst3 T T)) =>
   Prosa_Implementation_Refinements_ArrivalBound_valid_extrapolated_arrival_curve_T T
     inst_3
     inst_6
     inst_9
     inst_12
     inst_15 ac_prefix_vec)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       Prosa_Implementation_Refinements_Task_task_T T -> Bool

Arguments Prosa_Implementation_Refinements_EDF_Refinements_valid_arrivals_T T%_type_scope
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 tsk
```
