# `horizon_of_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.horizon_of_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.horizon_of_T`
- Certificate: `horizon_of_T_correspondence`

## Official Rocq

```coq
horizon_of_T : forall {T : Type}, T * seq (T * T) -> T

horizon_of_T is not universe polymorphic
Arguments horizon_of_T {T}%_type_scope ac_prefix_vec
horizon_of_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.horizon_of_T
Declared in library prosa.implementation.refinements.arrival_bound, line 43, characters 13-25
@horizon_of_T
     : forall T : Type, T * seq (T * T) -> T
```

Body:

```coq
horizon_of_T = fun T : Type => [eta @fst T (seq (T * T))]
     : forall {T : Type}, T * seq (T * T) -> T

Arguments horizon_of_T {T}%_type_scope ac_prefix_vec
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.horizon_of_T : {T : Type} → T × List (T × T) → T
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.horizon_of_T : {T : Type} → T × List (T × T) → T :=
fun {T} ac_prefix_vec => ac_prefix_vec.1
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T
     : forall T : Type, Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> T
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T@{} =
fun (T : Type) (ac_prefix_vec : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) =>
Prod_fst_inst3 T (List_inst1 (Prod_inst3 T T)) ac_prefix_vec
     : forall T : Type, Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> T

Arguments Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T T%_type_scope ac_prefix_vec
```
