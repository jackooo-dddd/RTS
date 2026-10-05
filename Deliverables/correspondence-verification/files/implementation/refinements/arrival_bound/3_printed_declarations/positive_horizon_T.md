# `positive_horizon_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.positive_horizon_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.positive_horizon_T`
- Certificate: `positive_horizon_T_correspondence`

## Official Rocq

```coq
positive_horizon_T : forall {T : Type}, zero_of T -> lt_of T -> T * seq (T * T) -> bool

positive_horizon_T is not universe polymorphic
Arguments positive_horizon_T {T}%_type_scope {zero_of0 lt_of0} ac_prefix
positive_horizon_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.positive_horizon_T
Declared in library prosa.implementation.refinements.arrival_bound, line 79, characters 13-31
@positive_horizon_T
     : forall T : Type, zero_of T -> lt_of T -> T * seq (T * T) -> bool
```

Body:

```coq
positive_horizon_T =
fun (T : Type) (zero_of0 : zero_of T) (lt_of0 : lt_of T) =>
let ArrivalCurvePrefix := (T * seq (T * T))%type in
fun ac_prefix : ArrivalCurvePrefix => (0 < @horizon_of_T T ac_prefix)%C
     : forall {T : Type}, zero_of T -> lt_of T -> T * seq (T * T) -> bool

Arguments positive_horizon_T {T}%_type_scope {zero_of0 lt_of0} ac_prefix
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.positive_horizon_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.lt_of T] → T × List (T × T) → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.positive_horizon_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.lt_of T] → T × List (T × T) → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.lt_of T]
    ac_prefix =>
  Prosa.Implementation.Refinements.Refinements.lt_op Prosa.Implementation.Refinements.Refinements.zero_op
    (Prosa.Implementation.Refinements.ArrivalBound.horizon_of_T ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_positive_horizon_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_positive_horizon_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_lt_of T)
  (ac_prefix : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) =>
Prosa_Implementation_Refinements_Refinements_lt_of_lt_op T
  inst_6
  (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
     inst_3)
  (Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T T ac_prefix)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalBound_positive_horizon_T T%_type_scope
  inst_3
  inst_6 
  ac_prefix
```
