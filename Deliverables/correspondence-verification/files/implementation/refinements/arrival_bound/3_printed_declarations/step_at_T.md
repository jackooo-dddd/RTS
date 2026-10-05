# `step_at_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.step_at_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.step_at_T`
- Certificate: `step_at_T_correspondence`

## Official Rocq

```coq
step_at_T : forall {T : Type}, zero_of T -> leq_of T -> T * seq (T * T) -> T -> T * T

step_at_T is not universe polymorphic
Arguments step_at_T {T}%_type_scope {zero_of0 leq_of0} ac_prefix_vec t
step_at_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.step_at_T
Declared in library prosa.implementation.refinements.arrival_bound, line 55, characters 13-22
@step_at_T
     : forall T : Type, zero_of T -> leq_of T -> T * seq (T * T) -> T -> T * T
```

Body:

```coq
step_at_T =
fun (T : Type) (zero_of0 : zero_of T) (leq_of0 : leq_of T) (ac_prefix_vec : T * seq (T * T)) (t : T) =>
@last (T * T) (0%C, 0%C) [seq step <- @steps_of_T T ac_prefix_vec | (step.1 <= t)%C]
     : forall {T : Type}, zero_of T -> leq_of T -> T * seq (T * T) -> T -> T * T

Arguments step_at_T {T}%_type_scope {zero_of0 leq_of0} ac_prefix_vec t
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.step_at_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → T → T × T
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.step_at_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × List (T × T) → T → T × T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.leq_of T]
    ac_prefix_vec t =>
  (List.filter (fun step => Prosa.Implementation.Refinements.Refinements.leq_op step.1 t)
        (Prosa.Implementation.Refinements.ArrivalBound.steps_of_T ac_prefix_vec)).getLastD
    (Prosa.Implementation.Refinements.Refinements.zero_op, Prosa.Implementation.Refinements.Refinements.zero_op)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_step_at_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> T -> Prod_inst3 T T
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_step_at_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (ac_prefix_vec : Prod_inst3 T (List_inst1 (Prod_inst3 T T))) (t : T) =>
List_getLastD_inst1 (Prod_inst3 T T)
  (List_filter_inst1 (Prod_inst3 T T)
     (fun step : Prod_inst3 T T =>
      Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
        inst_6
        (Prod_fst_inst3 T T step) t)
     (Prosa_Implementation_Refinements_ArrivalBound_steps_of_T T ac_prefix_vec))
  (Prod_mk_inst3 T T
     (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
        inst_3)
     (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
        inst_3))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T ->
       Prod_inst3 T (List_inst1 (Prod_inst3 T T)) -> T -> Prod_inst3 T T

Arguments Prosa_Implementation_Refinements_ArrivalBound_step_at_T T%_type_scope
  inst_3
  inst_6 
  ac_prefix_vec t
```
