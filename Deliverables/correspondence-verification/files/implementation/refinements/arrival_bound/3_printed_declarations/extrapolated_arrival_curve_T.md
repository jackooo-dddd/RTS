# `extrapolated_arrival_curve_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.extrapolated_arrival_curve_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.extrapolated_arrival_curve_T`
- Certificate: `extrapolated_arrival_curve_T_correspondence`

## Official Rocq

```coq
extrapolated_arrival_curve_T :
forall {T : Type},
zero_of T -> add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> T * seq (T * T) -> T -> T

extrapolated_arrival_curve_T is not universe polymorphic
Arguments extrapolated_arrival_curve_T {T}%_type_scope {zero_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0}
  ac_prefix_vec t
extrapolated_arrival_curve_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.extrapolated_arrival_curve_T
Declared in library prosa.implementation.refinements.arrival_bound, line 65, characters 13-41
@extrapolated_arrival_curve_T
     : forall T : Type,
       zero_of T -> add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> T * seq (T * T) -> T -> T
```

Body:

```coq
extrapolated_arrival_curve_T =
fun (T : Type) (zero_of0 : zero_of T) (add_of0 : add_of T) (mul_of0 : mul_of T) (div_of0 : div_of T)
  (mod_of0 : mod_of T) (leq_of0 : leq_of T) (ac_prefix_vec : T * seq (T * T)) (t : T) =>
let h := @horizon_of_T T ac_prefix_vec in
(t %/ h * @value_at_T T zero_of0 leq_of0 ac_prefix_vec h +
 @value_at_T T zero_of0 leq_of0 ac_prefix_vec (t %% h))%C
     : forall {T : Type},
       zero_of T -> add_of T -> mul_of T -> div_of T -> mod_of T -> leq_of T -> T * seq (T * T) -> T -> T

Arguments extrapolated_arrival_curve_T {T}%_type_scope {zero_of0 add_of0 mul_of0 div_of0 mod_of0 leq_of0}
  ac_prefix_vec t
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.extrapolated_arrival_curve_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.add_of T] →
      [Prosa.Implementation.Refinements.Refinements.mul_of T] →
        [Prosa.Implementation.Refinements.Refinements.div_of T] →
          [Prosa.Implementation.Refinements.Refinements.mod_of T] →
            [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.extrapolated_arrival_curve_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.add_of T] →
      [Prosa.Implementation.Refinements.Refinements.mul_of T] →
        [Prosa.Implementation.Refinements.Refinements.div_of T] →
          [Prosa.Implementation.Refinements.Refinements.mod_of T] →
            [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.add_of T]
    [Prosa.Implementation.Refinements.Refinements.mul_of T] [Prosa.Implementation.Refinements.Refinements.div_of T]
    [Prosa.Implementation.Refinements.Refinements.mod_of T] [Prosa.Implementation.Refinements.Refinements.leq_of T]
    ac_prefix_vec t =>
  have h := Prosa.Implementation.Refinements.ArrivalBound.horizon_of_T ac_prefix_vec;
  Prosa.Implementation.Refinements.Refinements.add_op
    (Prosa.Implementation.Refinements.Refinements.mul_op (Prosa.Implementation.Refinements.Refinements.div_op t h)
      (Prosa.Implementation.Refinements.ArrivalBound.value_at_T ac_prefix_vec h))
    (Prosa.Implementation.Refinements.ArrivalBound.value_at_T ac_prefix_vec
      (Prosa.Implementation.Refinements.Refinements.mod_op t h))
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_extrapolated_arrival_curve_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_mul_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_extrapolated_arrival_curve_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_add_of T)
  (inst_9 : 
   Prosa_Implementation_Refinements_Refinements_mul_of T)
  (inst_12 : 
   Prosa_Implementation_Refinements_Refinements_div_of T)
  (inst_15 : 
   Prosa_Implementation_Refinements_Refinements_mod_of T)
  (inst_18 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (ac_prefix_vec : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) (t : T) =>
let h := Prosa_Implementation_Refinements_ArrivalBound_horizon_of_T T ac_prefix_vec in
Prosa_Implementation_Refinements_Refinements_add_of_add_op T
  inst_6
  (Prosa_Implementation_Refinements_Refinements_mul_of_mul_op T
     inst_9
     (Prosa_Implementation_Refinements_Refinements_div_of_div_op T
        inst_12 t h)
     (Prosa_Implementation_Refinements_ArrivalBound_value_at_T T
        inst_3
        inst_18 ac_prefix_vec h))
  (Prosa_Implementation_Refinements_ArrivalBound_value_at_T T
     inst_3
     inst_18 ac_prefix_vec
     (Prosa_Implementation_Refinements_Refinements_mod_of_mod_op T
        inst_15 t h))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_mul_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> T -> T

Arguments Prosa_Implementation_Refinements_ArrivalBound_extrapolated_arrival_curve_T 
  T%_type_scope inst_3
  inst_6
  inst_9
  inst_12
  inst_15
  inst_18 
  ac_prefix_vec b
```
