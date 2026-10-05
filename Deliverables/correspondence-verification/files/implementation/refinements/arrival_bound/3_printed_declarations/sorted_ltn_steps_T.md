# `sorted_ltn_steps_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.sorted_ltn_steps_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.sorted_ltn_steps_T`
- Certificate: `sorted_ltn_steps_T_correspondence`

## Official Rocq

```coq
sorted_ltn_steps_T : forall {T : Type}, lt_of T -> T * seq (T * T) -> bool

sorted_ltn_steps_T is not universe polymorphic
Arguments sorted_ltn_steps_T {T}%_type_scope {lt_of0} ac_prefix
sorted_ltn_steps_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.sorted_ltn_steps_T
Declared in library prosa.implementation.refinements.arrival_bound, line 71, characters 13-31
@sorted_ltn_steps_T
     : forall T : Type, lt_of T -> T * seq (T * T) -> bool
```

Body:

```coq
sorted_ltn_steps_T =
fun (T : Type) (lt_of0 : lt_of T) =>
let ArrivalCurvePrefix := (T * seq (T * T))%type in
fun ac_prefix : ArrivalCurvePrefix => @sorted (T * T) (@ltn_steps_T T lt_of0) (@steps_of_T T ac_prefix)
     : forall {T : Type}, lt_of T -> T * seq (T * T) -> bool

Arguments sorted_ltn_steps_T {T}%_type_scope {lt_of0} ac_prefix
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.sorted_ltn_steps_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.lt_of T] → T × List (T × T) → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.sorted_ltn_steps_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.lt_of T] → T × List (T × T) → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.lt_of T] ac_prefix =>
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sortedBool
    Prosa.Implementation.Refinements.ArrivalBound.ltn_steps_T
    (Prosa.Implementation.Refinements.ArrivalBound.steps_of_T ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_sorted_ltn_steps_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_sorted_ltn_steps_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_lt_of T)
  (ac_prefix : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) =>
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1 (Prod_inst3 T T)
  (Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T T
     inst_3)
  (Prosa_Implementation_Refinements_ArrivalBound_steps_of_T T ac_prefix)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalBound_sorted_ltn_steps_T T%_type_scope
  inst_3 
  ac_prefix
```
