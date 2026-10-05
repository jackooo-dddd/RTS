# `large_horizon_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.large_horizon_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.large_horizon_T`
- Certificate: `large_horizon_T_correspondence`

## Official Rocq

```coq
large_horizon_T : forall {T : Type}, leq_of T -> T * seq (T * T) -> bool

large_horizon_T is not universe polymorphic
Arguments large_horizon_T {T}%_type_scope {leq_of0} ac_prefix
large_horizon_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.large_horizon_T
Declared in library prosa.implementation.refinements.arrival_bound, line 82, characters 13-28
@large_horizon_T
     : forall T : Type, leq_of T -> T * seq (T * T) -> bool
```

Body:

```coq
large_horizon_T =
fun (T : Type) (leq_of0 : leq_of T) =>
let ArrivalCurvePrefix := (T * seq (T * T))%type in
fun ac_prefix : ArrivalCurvePrefix =>
@all T ((@leq_op T leq_of0)^~ (@horizon_of_T T ac_prefix)) (@time_steps_of_T T ac_prefix)
     : forall {T : Type}, leq_of T -> T * seq (T * T) -> bool

Arguments large_horizon_T {T}%_type_scope {leq_of0} ac_prefix
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.large_horizon_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.large_horizon_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.leq_of T] ac_prefix =>
  (Prosa.Implementation.Refinements.ArrivalBound.time_steps_of_T ac_prefix).all fun s =>
    Prosa.Implementation.Refinements.Refinements.leq_op s
      (Prosa.Implementation.Refinements.ArrivalBound.horizon_of_T ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_large_horizon_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_large_horizon_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (ac_prefix : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) =>
List_all_inst1 T (Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T T ac_prefix)
  (fun s : T =>
   Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
     inst_3 s
     (Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T T ac_prefix))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalBound_large_horizon_T T%_type_scope
  inst_3 
  ac_prefix
```
