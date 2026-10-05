# `time_steps_of_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.time_steps_of_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.time_steps_of_T`
- Certificate: `time_steps_of_T_correspondence`

## Official Rocq

```coq
time_steps_of_T : forall {T : Type}, T * seq (T * T) -> seq T

time_steps_of_T is not universe polymorphic
Arguments time_steps_of_T {T}%_type_scope ac_prefix_vec
time_steps_of_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.time_steps_of_T
Declared in library prosa.implementation.refinements.arrival_bound, line 51, characters 13-28
@time_steps_of_T
     : forall T : Type, T * seq (T * T) -> seq T
```

Body:

```coq
time_steps_of_T =
fun (T : Type) (ac_prefix_vec : T * seq (T * T)) => [seq i.1 | i <- @steps_of_T T ac_prefix_vec]
     : forall {T : Type}, T * seq (T * T) -> seq T

Arguments time_steps_of_T {T}%_type_scope ac_prefix_vec
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.time_steps_of_T : {T : Type} → T × List (T × T) → List T
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.time_steps_of_T : {T : Type} → T × List (T × T) → List T :=
fun {T} ac_prefix_vec => List.map Prod.fst (Prosa.Implementation.Refinements.ArrivalBound.steps_of_T ac_prefix_vec)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T
     : forall T : Type, Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> List_inst1 T
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T@{} =
fun (T : Type) (ac_prefix_vec : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) =>
List_map_inst3 (Prod_inst3 T T) T (Prod_fst_inst3 T T)
  (Prosa_Implementation_Refinements_ArrivalBound_steps_of_T T ac_prefix_vec)
     : forall T : Type, Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> List_inst1 T

Arguments Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T T%_type_scope ac_prefix_vec
```
