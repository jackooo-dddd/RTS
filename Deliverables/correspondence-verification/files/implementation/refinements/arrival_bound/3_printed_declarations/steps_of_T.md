# `steps_of_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.steps_of_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.steps_of_T`
- Certificate: `steps_of_T_correspondence`

## Official Rocq

```coq
steps_of_T : forall {T : Type}, T * seq (T * T) -> seq (T * T)

steps_of_T is not universe polymorphic
Arguments steps_of_T {T}%_type_scope ac_prefix_vec
steps_of_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.steps_of_T
Declared in library prosa.implementation.refinements.arrival_bound, line 46, characters 13-23
@steps_of_T
     : forall T : Type, T * seq (T * T) -> seq (T * T)
```

Body:

```coq
steps_of_T =
fun T : Type => [eta @snd T (seq (T * T))]
     : forall {T : Type}, T * seq (T * T) -> seq (T * T)

Arguments steps_of_T {T}%_type_scope ac_prefix_vec
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.steps_of_T : {T : Type} → T × List (T × T) → List (T × T)
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.steps_of_T : {T : Type} → T × List (T × T) → List (T × T) :=
fun {T} ac_prefix_vec => ac_prefix_vec.2
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_steps_of_T
     : forall T : Type, Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> List_inst1 (Prod_inst3 T T)
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_steps_of_T@{} =
fun (T : Type) (ac_prefix_vec : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) =>
Prod_snd_inst3 T (List_inst1 (Prod_inst3 T T)) ac_prefix_vec
     : forall T : Type, Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> List_inst1 (Prod_inst3 T T)

Arguments Prosa_Implementation_Refinements_ArrivalBound_steps_of_T T%_type_scope ac_prefix_vec
```
