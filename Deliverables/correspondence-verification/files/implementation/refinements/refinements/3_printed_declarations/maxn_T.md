# `maxn_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.maxn_T`
- Lean: `Prosa.Implementation.Refinements.Refinements.maxn_T`
- Certificate: `maxn_T_correspondence`

## Official Rocq

```coq
maxn_T : forall {T : Type}, lt_of T -> T -> T -> T

maxn_T is not universe polymorphic
Arguments maxn_T {T}%_type_scope {lt_of0} m n
maxn_T is transparent
Expands to: Constant prosa.implementation.refinements.refinements.maxn_T
Declared in library prosa.implementation.refinements.refinements, line 69, characters 13-19
@maxn_T
     : forall T : Type, lt_of T -> T -> T -> T
```

Body:

```coq
maxn_T =
fun (T : Type) (lt_of0 : lt_of T) (m n : T) => if (m < n)%C then n else m
     : forall {T : Type}, lt_of T -> T -> T -> T

Arguments maxn_T {T}%_type_scope {lt_of0} m n
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.maxn_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.lt_of T] → T → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.maxn_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.lt_of T] → T → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.lt_of T] m n =>
  if Prosa.Implementation.Refinements.Refinements.lt_op m n = true then n else m
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_maxn_T
     : forall T : Type, Prosa_Implementation_Refinements_Refinements_lt_of T -> T -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_maxn_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_lt_of T)
  (m n : T) =>
ite T
  (@eq Bool
     (Prosa_Implementation_Refinements_Refinements_lt_of_lt_op T
        inst_3 m n)
     Bool_true)
  (instDecidableEqBool
     (Prosa_Implementation_Refinements_Refinements_lt_of_lt_op T
        inst_3 m n)
     Bool_true)
  n m
     : forall T : Type, Prosa_Implementation_Refinements_Refinements_lt_of T -> T -> T -> T

Arguments Prosa_Implementation_Refinements_Refinements_maxn_T T%_type_scope
  inst_3 
  a____at____internal__hyg0 a____at____internal__hyg0
```
