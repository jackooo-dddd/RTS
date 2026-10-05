# `shift_points_pos_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.shift_points_pos_T`
- Lean: `Prosa.Implementation.Refinements.Refinements.shift_points_pos_T`
- Certificate: `shift_points_pos_T_correspondence`

## Official Rocq

```coq
shift_points_pos_T : forall {T : Type}, add_of T -> seq T -> T -> seq T

shift_points_pos_T is not universe polymorphic
Arguments shift_points_pos_T {T}%_type_scope {add_of0} xs%_seq_scope s
shift_points_pos_T is transparent
Expands to: Constant prosa.implementation.refinements.refinements.shift_points_pos_T
Declared in library prosa.implementation.refinements.refinements, line 247, characters 13-31
@shift_points_pos_T
     : forall T : Type, add_of T -> seq T -> T -> seq T
```

Body:

```coq
shift_points_pos_T =
fun (T : Type) (add_of0 : add_of T) (xs : seq T) (s : T) => [seq (s + x)%C | x <- xs]
     : forall {T : Type}, add_of T -> seq T -> T -> seq T

Arguments shift_points_pos_T {T}%_type_scope {add_of0} xs%_seq_scope s
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.shift_points_pos_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.add_of T] → List T → T → List T
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.shift_points_pos_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.add_of T] → List T → T → List T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.add_of T] xs s =>
  List.map (fun x => Prosa.Implementation.Refinements.Refinements.add_op s x) xs
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_shift_points_pos_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_add_of T -> List_inst1 T -> T -> List_inst1 T
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_shift_points_pos_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_add_of T)
  (xs : List_inst1 T) (s : T) =>
List_map_inst3 T T
  (fun x : T =>
   Prosa_Implementation_Refinements_Refinements_add_of_add_op T
     inst_3 s x)
  xs
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_add_of T -> List_inst1 T -> T -> List_inst1 T

Arguments Prosa_Implementation_Refinements_Refinements_shift_points_pos_T T%_type_scope
  inst_3 
  xs s
```
