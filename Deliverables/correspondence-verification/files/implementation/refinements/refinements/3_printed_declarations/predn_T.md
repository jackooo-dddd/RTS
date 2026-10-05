# `predn_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.predn_T`
- Lean: `Prosa.Implementation.Refinements.Refinements.predn_T`
- Certificate: `predn_T_correspondence`

## Official Rocq

```coq
predn_T : forall {T : Type}, one_of T -> sub_of T -> T -> T

predn_T is not universe polymorphic
Arguments predn_T {T}%_type_scope {one_of0 sub_of0} n
predn_T is transparent
Expands to: Constant prosa.implementation.refinements.refinements.predn_T
Declared in library prosa.implementation.refinements.refinements, line 66, characters 13-20
@predn_T
     : forall T : Type, one_of T -> sub_of T -> T -> T
```

Body:

```coq
predn_T =
fun (T : Type) (one_of0 : one_of T) (sub_of0 : sub_of T) => (@sub_op T sub_of0)^~ 1%C
     : forall {T : Type}, one_of T -> sub_of T -> T -> T

Arguments predn_T {T}%_type_scope {one_of0 sub_of0} n
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.predn_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.sub_of T] → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.predn_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.one_of T] →
    [Prosa.Implementation.Refinements.Refinements.sub_of T] → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.one_of T] [Prosa.Implementation.Refinements.Refinements.sub_of T]
    n =>
  Prosa.Implementation.Refinements.Refinements.sub_op n Prosa.Implementation.Refinements.Refinements.one_op
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_predn_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_sub_of T -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_predn_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_one_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_sub_of T)
  (n : T) =>
Prosa_Implementation_Refinements_Refinements_sub_of_sub_op T
  inst_6 n
  (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
     inst_3)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_sub_of T -> T -> T

Arguments Prosa_Implementation_Refinements_Refinements_predn_T T%_type_scope
  inst_3
  inst_6 
  a____at____internal__hyg0
```
