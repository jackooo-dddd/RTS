# `leq_steps_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.leq_steps_T`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T`
- Certificate: `leq_steps_T_correspondence`

## Official Rocq

```coq
leq_steps_T : forall {T : Type}, leq_of T -> T * T -> T * T -> bool

leq_steps_T is not universe polymorphic
Arguments leq_steps_T {T}%_type_scope {leq_of0} a b
leq_steps_T is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.leq_steps_T
Declared in library prosa.implementation.refinements.arrival_bound, line 76, characters 13-24
@leq_steps_T
     : forall T : Type, leq_of T -> T * T -> T * T -> bool
```

Body:

```coq
leq_steps_T =
fun (T : Type) (leq_of0 : leq_of T) (a b : T * T) => (a.1 <= b.1)%C && (a.2 <= b.2)%C
     : forall {T : Type}, leq_of T -> T * T -> T * T -> bool

Arguments leq_steps_T {T}%_type_scope {leq_of0} a b
```

## Lean

```lean
@Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × T → T × T → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.leq_steps_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.leq_of T] → T × T → T × T → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.leq_of T] a b =>
  Prosa.Implementation.Refinements.Refinements.leq_op a.1 b.1 &&
    Prosa.Implementation.Refinements.Refinements.leq_op a.2 b.2
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_leq_of T -> Prod_inst3 T T -> Prod_inst3 T T -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_leq_of T)
  (a b : Prod_inst3 T T) =>
Bool_and
  (Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
     inst_3
     (Prod_fst_inst3 T T a) (Prod_fst_inst3 T T b))
  (Prosa_Implementation_Refinements_Refinements_leq_of_leq_op T
     inst_3
     (Prod_snd_inst3 T T a) (Prod_snd_inst3 T T b))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_leq_of T -> Prod_inst3 T T -> Prod_inst3 T T -> Bool

Arguments Prosa_Implementation_Refinements_ArrivalBound_leq_steps_T T%_type_scope
  inst_3 
  a b
```
