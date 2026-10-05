# `ltn_steps_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.ltn_steps_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.ltn_steps_T`
- Certificate: `ltn_steps_T_correspondence`

## Official Rocq

```coq
ltn_steps_T : forall {T : Type}, lt_of T -> T * T -> T * T -> bool

ltn_steps_T is not universe polymorphic
Arguments ltn_steps_T {T}%_type_scope {lt_of0} a b
ltn_steps_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.ltn_steps_T
Declared in library prosa.implementation.refinements.arrival_bound, line 70, characters 13-24
@ltn_steps_T
     : forall T : Type, lt_of T -> T * T -> T * T -> bool
```

Body:

```coq
ltn_steps_T =
fun (T : Type) (lt_of0 : lt_of T) (a b : T * T) => (a.1 < b.1)%C && (a.2 < b.2)%C
     : forall {T : Type}, lt_of T -> T * T -> T * T -> bool

Arguments ltn_steps_T {T}%_type_scope {lt_of0} a b
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.ltn_steps_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.lt_of T] → T × T → T × T → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.ltn_steps_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.lt_of T] → T × T → T × T → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.lt_of T] a b =>
  Prosa.Implementation.Refinements.Refinements.lt_op a.1 b.1 &&
    Prosa.Implementation.Refinements.Refinements.lt_op a.2 b.2
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_lt_of T -> Prod_inst3 T T -> Prod_inst3 T T -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_lt_of T)
  (a b : Prod_inst3 T T) =>
Bool_and
  (Prosa_Implementation_Refinements_Refinements_lt_of_lt_op T
     inst_3
     (Prod_fst_inst3 T T a) (Prod_fst_inst3 T T b))
  (Prosa_Implementation_Refinements_Refinements_lt_of_lt_op T
     inst_3
     (Prod_snd_inst3 T T a) (Prod_snd_inst3 T T b))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_lt_of T -> Prod_inst3 T T -> Prod_inst3 T T -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalBound_ltn_steps_T T%_type_scope
  inst_3 
  a b
```
