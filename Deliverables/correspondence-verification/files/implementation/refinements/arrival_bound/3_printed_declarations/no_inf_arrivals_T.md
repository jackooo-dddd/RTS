# `no_inf_arrivals_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.no_inf_arrivals_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.no_inf_arrivals_T`
- Certificate: `no_inf_arrivals_T_correspondence`

## Official Rocq

```coq
no_inf_arrivals_T : forall {T : Type}, zero_of T -> eq_of T -> leq_of T -> T * seq (T * T) -> bool

no_inf_arrivals_T is not universe polymorphic
Arguments no_inf_arrivals_T {T}%_type_scope {zero_of0 eq_of0 leq_of0} ac_prefix
no_inf_arrivals_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.no_inf_arrivals_T
Declared in library prosa.implementation.refinements.arrival_bound, line 86, characters 13-30
@no_inf_arrivals_T
     : forall T : Type, zero_of T -> eq_of T -> leq_of T -> T * seq (T * T) -> bool
```

Body:

```coq
no_inf_arrivals_T =
fun (T : Type) (zero_of0 : zero_of T) (eq_of0 : eq_of T) (leq_of0 : leq_of T) =>
let ArrivalCurvePrefix := (T * seq (T * T))%type in
fun ac_prefix : ArrivalCurvePrefix => (@value_at_T T zero_of0 leq_of0 ac_prefix 0 == 0)%C
     : forall {T : Type}, zero_of T -> eq_of T -> leq_of T -> T * seq (T * T) -> bool

Arguments no_inf_arrivals_T {T}%_type_scope {zero_of0 eq_of0 leq_of0} ac_prefix
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.no_inf_arrivals_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.eq_of T] →
      [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.no_inf_arrivals_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.eq_of T] →
      [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.eq_of T]
    [Prosa.Implementation.Refinements.Refinements.leq_of T] ac_prefix =>
  Prosa.Implementation.Refinements.Refinements.eq_op
    (Prosa.Implementation.Refinements.ArrivalBound.value_at_T ac_prefix
      Prosa.Implementation.Refinements.Refinements.zero_op)
    Prosa.Implementation.Refinements.Refinements.zero_op
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_no_inf_arrivals_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_no_inf_arrivals_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_eq_of T)
  (inst_9 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (ac_prefix : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) =>
Prosa_Implementation_Refinements_Refinements_eq_of_eq_op T
  inst_6
  (Prosa_Implementation_Refinements_ArrivalBound_value_at_T T
     inst_3
     inst_9 ac_prefix
     (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
        inst_3))
  (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
     inst_3)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalBound_no_inf_arrivals_T T%_type_scope
  inst_3
  inst_6
  inst_9 
  ac_prefix
```
