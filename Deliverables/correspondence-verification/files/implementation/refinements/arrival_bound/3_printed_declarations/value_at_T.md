# `value_at_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.value_at_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.value_at_T`
- Certificate: `value_at_T_correspondence`

## Official Rocq

```coq
value_at_T : forall {T : Type}, zero_of T -> leq_of T -> T * seq (T * T) -> T -> T

value_at_T is not universe polymorphic
Arguments value_at_T {T}%_type_scope {zero_of0 leq_of0} ac_prefix_vec t
value_at_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.value_at_T
Declared in library prosa.implementation.refinements.arrival_bound, line 60, characters 13-23
@value_at_T
     : forall T : Type, zero_of T -> leq_of T -> T * seq (T * T) -> T -> T
```

Body:

```coq
value_at_T =
fun (T : Type) (zero_of0 : zero_of T) (leq_of0 : leq_of T) (ac_prefix_vec : T * seq (T * T)) (t : T) =>
(@step_at_T T zero_of0 leq_of0 ac_prefix_vec t).2
     : forall {T : Type}, zero_of T -> leq_of T -> T * seq (T * T) -> T -> T

Arguments value_at_T {T}%_type_scope {zero_of0 leq_of0} ac_prefix_vec t
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.value_at_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.value_at_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.leq_of T]
    ac_prefix_vec t =>
  (Prosa.Implementation.Refinements.ArrivalBound.step_at_T ac_prefix_vec t).2
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_value_at_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_value_at_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (ac_prefix_vec : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) (t : T) =>
Prod_snd_inst3 T T
  (Prosa_Implementation_Refinements_ArrivalBound_step_at_T T
     inst_3
     inst_6 ac_prefix_vec t)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> T -> T

Arguments Prosa_Implementation_Refinements_ArrivalBound_value_at_T T%_type_scope
  inst_3
  inst_6 
  ac_prefix_vec e
```
