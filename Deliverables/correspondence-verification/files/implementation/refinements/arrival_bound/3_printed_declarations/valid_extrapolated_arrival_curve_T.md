# `valid_extrapolated_arrival_curve_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.valid_extrapolated_arrival_curve_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.valid_extrapolated_arrival_curve_T`
- Certificate: `valid_extrapolated_arrival_curve_T_correspondence`

## Official Rocq

```coq
valid_extrapolated_arrival_curve_T :
forall {T : Type}, zero_of T -> one_of T -> eq_of T -> leq_of T -> lt_of T -> T * seq (T * T) -> bool

valid_extrapolated_arrival_curve_T is not universe polymorphic
Arguments valid_extrapolated_arrival_curve_T {T}%_type_scope {zero_of0 one_of0 eq_of0 leq_of0 lt_of0}
  ac_prefix
valid_extrapolated_arrival_curve_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.valid_extrapolated_arrival_curve_T
Declared in library prosa.implementation.refinements.arrival_bound, line 96, characters 13-47
@valid_extrapolated_arrival_curve_T
     : forall T : Type, zero_of T -> one_of T -> eq_of T -> leq_of T -> lt_of T -> T * seq (T * T) -> bool
```

Body:

```coq
valid_extrapolated_arrival_curve_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (eq_of0 : eq_of T) (leq_of0 : leq_of T)
  (lt_of0 : lt_of T) =>
let ArrivalCurvePrefix := (T * seq (T * T))%type in
fun ac_prefix : ArrivalCurvePrefix =>
@positive_horizon_T T zero_of0 lt_of0 ac_prefix && @large_horizon_T T leq_of0 ac_prefix &&
@no_inf_arrivals_T T zero_of0 eq_of0 leq_of0 ac_prefix && @specified_bursts_T T one_of0 eq_of0 ac_prefix &&
@sorted_ltn_steps_T T lt_of0 ac_prefix
     : forall {T : Type}, zero_of T -> one_of T -> eq_of T -> leq_of T -> lt_of T -> T * seq (T * T) -> bool

Arguments valid_extrapolated_arrival_curve_T {T}%_type_scope {zero_of0 one_of0 eq_of0 leq_of0 lt_of0}
  ac_prefix
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.valid_extrapolated_arrival_curve_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.eq_of T] →
        [Prosa.Implementation.Refinements.Refinements.leq_of T] →
          [Prosa.Implementation.Refinements.Refinements.lt_of T] → T × List (T × T) → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.valid_extrapolated_arrival_curve_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.eq_of T] →
        [Prosa.Implementation.Refinements.Refinements.leq_of T] →
          [Prosa.Implementation.Refinements.Refinements.lt_of T] → T × List (T × T) → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.eq_of T] [Prosa.Implementation.Refinements.Refinements.leq_of T]
    [Prosa.Implementation.Refinements.Refinements.lt_of T] ac_prefix =>
  Prosa.Implementation.Refinements.ArrivalBound.positive_horizon_T ac_prefix &&
          Prosa.Implementation.Refinements.ArrivalBound.large_horizon_T ac_prefix &&
        Prosa.Implementation.Refinements.ArrivalBound.no_inf_arrivals_T ac_prefix &&
      Prosa.Implementation.Refinements.ArrivalBound.specified_bursts_T ac_prefix &&
    Prosa.Implementation.Refinements.ArrivalBound.sorted_ltn_steps_T ac_prefix
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_valid_extrapolated_arrival_curve_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_valid_extrapolated_arrival_curve_T@{} =
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
  (ac_prefix : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) =>
Bool_and
  (Bool_and
     (Bool_and
        (Bool_and
           (Prosa_Implementation_Refinements_ArrivalBound_positive_horizon_T T
              inst_3
              inst_15 ac_prefix)
           (Prosa_Implementation_Refinements_ArrivalBound_large_horizon_T T
              inst_12 ac_prefix))
        (Prosa_Implementation_Refinements_ArrivalBound_no_inf_arrivals_T T
           inst_3
           inst_9
           inst_12 ac_prefix))
     (Prosa_Implementation_Refinements_ArrivalBound_specified_bursts_T T
        inst_6
        inst_9 ac_prefix))
  (Prosa_Implementation_Refinements_ArrivalBound_sorted_ltn_steps_T T
     inst_15 ac_prefix)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prosa_Implementation_Refinements_Refinements_lt_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalBound_valid_extrapolated_arrival_curve_T 
  T%_type_scope inst_3
  inst_6
  inst_9
  inst_12
  inst_15 
  ac_prefix
```
