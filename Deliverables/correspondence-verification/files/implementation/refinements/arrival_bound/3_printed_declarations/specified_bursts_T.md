# `specified_bursts_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.specified_bursts_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.specified_bursts_T`
- Certificate: `specified_bursts_T_correspondence`

## Official Rocq

```coq
specified_bursts_T : forall {T : Type}, one_of T -> eq_of T -> T * seq (T * T) -> bool

specified_bursts_T is not universe polymorphic
Arguments specified_bursts_T {T}%_type_scope {one_of0 eq_of0} ac_prefix
specified_bursts_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.specified_bursts_T
Declared in library prosa.implementation.refinements.arrival_bound, line 91, characters 13-31
@specified_bursts_T
     : forall T : Type, one_of T -> eq_of T -> T * seq (T * T) -> bool
```

Body:

```coq
specified_bursts_T =
fun (T : Type) (one_of0 : one_of T) (eq_of0 : eq_of T) =>
let ArrivalCurvePrefix := (T * seq (T * T))%type in
fun ac_prefix : ArrivalCurvePrefix =>
@has T ((@Refinements.Op.eq_op T eq_of0)^~ 1%C) (@time_steps_of_T T ac_prefix)
     : forall {T : Type}, one_of T -> eq_of T -> T * seq (T * T) -> bool

Arguments specified_bursts_T {T}%_type_scope {one_of0 eq_of0} ac_prefix
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.specified_bursts_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.eq_of T] → T × List (T × T) → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.specified_bursts_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.eq_of T] → T × List (T × T) → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.one_of T] [Prosa.Implementation.Refinements.Refinements.eq_of T]
    ac_prefix =>
  (Prosa.Implementation.Refinements.ArrivalBound.time_steps_of_T ac_prefix).any fun step =>
    Prosa.Implementation.Refinements.Refinements.eq_op step Prosa.Implementation.Refinements.Refinements.one_op
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_specified_bursts_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_specified_bursts_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_one_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_eq_of T)
  (ac_prefix : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) =>
List_any_inst1 T (Prosa_Implementation_Refinements_ArrivalBound_time_steps_of_T T ac_prefix)
  (fun step : T =>
   Prosa_Implementation_Refinements_Refinements_eq_of_eq_op T
     inst_6 step
     (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
        inst_3))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalBound_specified_bursts_T T%_type_scope
  inst_3
  inst_6 
  ac_prefix
```
