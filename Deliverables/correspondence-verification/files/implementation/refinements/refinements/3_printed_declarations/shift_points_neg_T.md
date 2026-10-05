# `shift_points_neg_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.shift_points_neg_T`
- Lean: `Prosa.Implementation.Refinements.Refinements.shift_points_neg_T`
- Certificate: `shift_points_neg_T_correspondence`

## Official Rocq

```coq
shift_points_neg_T : forall {T : Type}, sub_of T -> leq_of T -> seq T -> T -> seq T

shift_points_neg_T is not universe polymorphic
Arguments shift_points_neg_T {T}%_type_scope {sub_of0 leq_of0} xs%_seq_scope s
shift_points_neg_T is transparent
Expands to: Constant prosa.implementation.refinements.refinements.shift_points_neg_T
Declared in library prosa.implementation.refinements.refinements, line 251, characters 13-31
@shift_points_neg_T
     : forall T : Type, sub_of T -> leq_of T -> seq T -> T -> seq T
```

Body:

```coq
shift_points_neg_T =
fun (T : Type) (sub_of0 : sub_of T) (leq_of0 : leq_of T) (xs : seq T) (s : T) =>
let nonsmall := [seq x <- xs | (s <= x)%C] in [seq (x - s)%C | x <- nonsmall]
     : forall {T : Type}, sub_of T -> leq_of T -> seq T -> T -> seq T

Arguments shift_points_neg_T {T}%_type_scope {sub_of0 leq_of0} xs%_seq_scope s
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.shift_points_neg_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.sub_of T] →
    [Prosa.Implementation.Refinements.Refinements.leq_of T] → List T → T → List T
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.shift_points_neg_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.sub_of T] →
    [Prosa.Implementation.Refinements.Refinements.leq_of T] → List T → T → List T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.sub_of T] [Prosa.Implementation.Refinements.Refinements.leq_of T]
    xs s =>
  have nonsmall := List.filter (fun x => Prosa.Implementation.Refinements.Refinements.leq_op s x) xs;
  List.map (fun x => Prosa.Implementation.Refinements.Refinements.sub_op x s) nonsmall
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_shift_points_neg_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_sub_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T -> List_inst1 T -> T -> List_inst1 T
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_shift_points_neg_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_sub_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (xs : List_inst1 T) (s : T) =>
let nonsmall :=
  List_filter_inst1 T
    (fun x : T =>
     Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
       inst_6 s x)
    xs
  in
List_map_inst3 T T
  (fun x : T =>
   Prosa_Implementation_Refinements_Refinements_sub_of_sub_op T
     inst_3 x s)
  nonsmall
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_sub_of T ->
       Prosa_Implementation_Refinements_Refinements_leq_of T -> List_inst1 T -> T -> List_inst1 T

Arguments Prosa_Implementation_Refinements_Refinements_shift_points_neg_T T%_type_scope
  inst_3
  inst_6 
  xs s
```
