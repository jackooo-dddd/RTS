# `size_T`

- Kind (Rocq): Fixpoint
- Rocq: `prosa.implementation.refinements.refinements.size_T`
- Lean: `Prosa.Implementation.Refinements.Refinements.size_T`
- Certificate: `size_T_correspondence`

## Official Rocq

```coq
size_T : forall {T : Type}, zero_of T -> one_of T -> add_of T -> forall {X : Type}, seq X -> T

size_T is not universe polymorphic
Arguments size_T {T}%_type_scope {zero_of0 one_of0 add_of0} {X}%_type_scope s%_seq_scope
size_T is transparent
Expands to: Constant prosa.implementation.refinements.refinements.size_T
Declared in library prosa.implementation.refinements.refinements, line 240, characters 11-17
@size_T
     : forall T : Type, zero_of T -> one_of T -> add_of T -> forall X : Type, seq X -> T
```

Body:

```coq
size_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (add_of0 : add_of T) =>
fix size_T (X : Type) (s : seq X) {struct s} : T :=
  match s with
  | [::] => 0%C
  | _ :: s' => (1 + size_T X s')%C
  end
     : forall {T : Type}, zero_of T -> one_of T -> add_of T -> forall {X : Type}, seq X -> T

Arguments size_T {T}%_type_scope {zero_of0 one_of0 add_of0} {X}%_type_scope s%_seq_scope
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.size_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] → {X : Type} → List X → T
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.size_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] → {X : Type} → List X → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.add_of T] {X} x =>
  List.brecOn x Prosa.Implementation.Refinements.Refinements.size_T._f
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_size_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T -> forall X : Type, List_inst1 X -> T
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_size_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_one_of T)
  (inst_9 : 
   Prosa_Implementation_Refinements_Refinements_add_of T)
  (X : Type) (x____at___Prosa_Implementation_Refinements_Refinements3254396549__hygCtx__hyg17 : List_inst1 X) =>
List_brecOn_inst2 X (fun _ : List_inst1 X => T)
  x____at___Prosa_Implementation_Refinements_Refinements3254396549__hygCtx__hyg17
  (Prosa_Implementation_Refinements_Refinements_size_T__f T
     inst_3
     inst_6
     inst_9 X)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T -> forall X : Type, List_inst1 X -> T

Arguments Prosa_Implementation_Refinements_Refinements_size_T T%_type_scope
  inst_3
  inst_6
  inst_9 
  X%_type_scope a____at____internal__hyg0
```
