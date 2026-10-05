# `dvdn_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.dvdn_T`
- Lean: `Prosa.Implementation.Refinements.Refinements.dvdn_T`
- Certificate: `dvdn_T_correspondence`

## Official Rocq

```coq
dvdn_T : forall {T : Type}, zero_of T -> mod_of T -> eq_of T -> T -> T -> bool

dvdn_T is not universe polymorphic
Arguments dvdn_T {T}%_type_scope {zero_of0 mod_of0 eq_of0} d m
dvdn_T is transparent
Expands to: Constant prosa.implementation.refinements.refinements.dvdn_T
Declared in library prosa.implementation.refinements.refinements, line 73, characters 13-19
@dvdn_T
     : forall T : Type, zero_of T -> mod_of T -> eq_of T -> T -> T -> bool
```

Body:

```coq
dvdn_T =
fun (T : Type) (zero_of0 : zero_of T) (mod_of0 : mod_of T) (eq_of0 : eq_of T) (d m : T) => (m %% d == 0)%C
     : forall {T : Type}, zero_of T -> mod_of T -> eq_of T -> T -> T -> bool

Arguments dvdn_T {T}%_type_scope {zero_of0 mod_of0 eq_of0} d m
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.dvdn_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.mod_of T] →
      [Prosa.Implementation.Refinements.Refinements.eq_of T] → T → T → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.dvdn_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.mod_of T] →
      [Prosa.Implementation.Refinements.Refinements.eq_of T] → T → T → Bool :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.mod_of T]
    [Prosa.Implementation.Refinements.Refinements.eq_of T] d m =>
  Prosa.Implementation.Refinements.Refinements.eq_op (Prosa.Implementation.Refinements.Refinements.mod_op m d)
    Prosa.Implementation.Refinements.Refinements.zero_op
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_dvdn_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T -> T -> T -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_dvdn_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_mod_of T)
  (inst_9 : 
   Prosa_Implementation_Refinements_Refinements_eq_of T)
  (d m : T) =>
Prosa_Implementation_Refinements_Refinements_eq_of_eq_op T
  inst_9
  (Prosa_Implementation_Refinements_Refinements_mod_of_mod_op T
     inst_6 m d)
  (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op T
     inst_3)
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T -> T -> T -> Bool

Arguments Prosa_Implementation_Refinements_Refinements_dvdn_T T%_type_scope
  inst_3
  inst_6
  inst_9 
  d m
```
