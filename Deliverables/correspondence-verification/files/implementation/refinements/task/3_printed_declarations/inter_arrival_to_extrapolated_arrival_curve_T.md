# `inter_arrival_to_extrapolated_arrival_curve_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.inter_arrival_to_extrapolated_arrival_curve_T`
- Lean: `Prosa.Implementation.Refinements.Task.inter_arrival_to_extrapolated_arrival_curve_T`
- Certificate: `inter_arrival_to_extrapolated_arrival_curve_T_correspondence`

## Official Rocq

```coq
inter_arrival_to_extrapolated_arrival_curve_T : forall {T : Type}, one_of T -> T -> T * seq (T * T)

inter_arrival_to_extrapolated_arrival_curve_T is not universe polymorphic
Arguments inter_arrival_to_extrapolated_arrival_curve_T {T}%_type_scope {one_of0} p
inter_arrival_to_extrapolated_arrival_curve_T is transparent
Expands to: Constant prosa.implementation.refinements.task.inter_arrival_to_extrapolated_arrival_curve_T
Declared in library prosa.implementation.refinements.task, line 49, characters 13-58
@inter_arrival_to_extrapolated_arrival_curve_T
     : forall T : Type, one_of T -> T -> T * seq (T * T)
```

Body:

```coq
inter_arrival_to_extrapolated_arrival_curve_T =
fun (T : Type) (one_of0 : one_of T) => (@pair T (seq (T * T)))^~ [:: (1%C, 1%C)]
     : forall {T : Type}, one_of T -> T -> T * seq (T * T)

Arguments inter_arrival_to_extrapolated_arrival_curve_T {T}%_type_scope {one_of0} p
```

## Lean

```lean
@Prosa.Implementation.Refinements.Task.inter_arrival_to_extrapolated_arrival_curve_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] → T → T × List (T × T)
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.inter_arrival_to_extrapolated_arrival_curve_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] → T → T × List (T × T) :=
fun {T} [Prosa.Implementation.Refinements.Refinements.one_of T] p =>
  (p, [(Prosa.Implementation.Refinements.Refinements.one_op, Prosa.Implementation.Refinements.Refinements.one_op)])
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_inter_arrival_to_extrapolated_arrival_curve_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       T -> Prod_inst3 T (List_inst1 (Prod_inst3 T T))
```

Body:

```coq
Prosa_Implementation_Refinements_Task_inter_arrival_to_extrapolated_arrival_curve_T@{} =
fun (T : Type)
  (inst_3 : Prosa_Implementation_Refinements_Refinements_one_of
                                                                                T)
  (p : T) =>
Prod_mk_inst3 T (List_inst1 (Prod_inst3 T T)) p
  (List_cons_inst1 (Prod_inst3 T T)
     (Prod_mk_inst3 T T
        (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
           inst_3)
        (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
           inst_3))
     (List_nil_inst1 (Prod_inst3 T T)))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       T -> Prod_inst3 T (List_inst1 (Prod_inst3 T T))

Arguments Prosa_Implementation_Refinements_Task_inter_arrival_to_extrapolated_arrival_curve_T 
  T%_type_scope inst_3 
  p
```
