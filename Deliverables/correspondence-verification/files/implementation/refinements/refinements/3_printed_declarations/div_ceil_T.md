# `div_ceil_T`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.div_ceil_T`
- Lean: `Prosa.Implementation.Refinements.Refinements.div_ceil_T`
- Certificate: `div_ceil_T_correspondence`

## Official Rocq

```coq
div_ceil_T :
forall {T : Type}, zero_of T -> one_of T -> add_of T -> div_of T -> mod_of T -> eq_of T -> T -> T -> T

div_ceil_T is not universe polymorphic
Arguments div_ceil_T {T}%_type_scope {zero_of0 one_of0 add_of0 div_of0 mod_of0 eq_of0} a b
div_ceil_T is transparent
Expands to: Constant prosa.implementation.refinements.refinements.div_ceil_T
Declared in library prosa.implementation.refinements.refinements, line 76, characters 13-23
@div_ceil_T
     : forall T : Type, zero_of T -> one_of T -> add_of T -> div_of T -> mod_of T -> eq_of T -> T -> T -> T
```

Body:

```coq
div_ceil_T =
fun (T : Type) (zero_of0 : zero_of T) (one_of0 : one_of T) (add_of0 : add_of T) (div_of0 : div_of T)
  (mod_of0 : mod_of T) (eq_of0 : eq_of T) (a b : T) =>
if @dvdn_T T zero_of0 mod_of0 eq_of0 b a then (a %/ b)%C else (1 + a %/ b)%C
     : forall {T : Type}, zero_of T -> one_of T -> add_of T -> div_of T -> mod_of T -> eq_of T -> T -> T -> T

Arguments div_ceil_T {T}%_type_scope {zero_of0 one_of0 add_of0 div_of0 mod_of0 eq_of0} a b
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.div_ceil_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] →
        [Prosa.Implementation.Refinements.Refinements.div_of T] →
          [Prosa.Implementation.Refinements.Refinements.mod_of T] →
            [Prosa.Implementation.Refinements.Refinements.eq_of T] → T → T → T
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.div_ceil_T : {T : Type} →
  [Prosa.Implementation.Refinements.Refinements.zero_of T] →
    [Prosa.Implementation.Refinements.Refinements.one_of T] →
      [Prosa.Implementation.Refinements.Refinements.add_of T] →
        [Prosa.Implementation.Refinements.Refinements.div_of T] →
          [Prosa.Implementation.Refinements.Refinements.mod_of T] →
            [Prosa.Implementation.Refinements.Refinements.eq_of T] → T → T → T :=
fun {T} [Prosa.Implementation.Refinements.Refinements.zero_of T] [Prosa.Implementation.Refinements.Refinements.one_of T]
    [Prosa.Implementation.Refinements.Refinements.add_of T] [Prosa.Implementation.Refinements.Refinements.div_of T]
    [Prosa.Implementation.Refinements.Refinements.mod_of T] [Prosa.Implementation.Refinements.Refinements.eq_of T] a
    b =>
  if Prosa.Implementation.Refinements.Refinements.dvdn_T b a = true then
    Prosa.Implementation.Refinements.Refinements.div_op a b
  else
    Prosa.Implementation.Refinements.Refinements.add_op Prosa.Implementation.Refinements.Refinements.one_op
      (Prosa.Implementation.Refinements.Refinements.div_op a b)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_div_ceil_T
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T -> T -> T -> T
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_div_ceil_T@{} =
fun (T : Type)
  (inst_3 : 
   Prosa_Implementation_Refinements_Refinements_zero_of T)
  (inst_6 : 
   Prosa_Implementation_Refinements_Refinements_one_of T)
  (inst_9 : 
   Prosa_Implementation_Refinements_Refinements_add_of T)
  (inst_12 : 
   Prosa_Implementation_Refinements_Refinements_div_of T)
  (inst_15 : 
   Prosa_Implementation_Refinements_Refinements_mod_of T)
  (inst_18 : 
   Prosa_Implementation_Refinements_Refinements_eq_of T)
  (a b : T) =>
ite T
  (@eq Bool
     (Prosa_Implementation_Refinements_Refinements_dvdn_T T
        inst_3
        inst_15
        inst_18 b a)
     Bool_true)
  (instDecidableEqBool
     (Prosa_Implementation_Refinements_Refinements_dvdn_T T
        inst_3
        inst_15
        inst_18 b a)
     Bool_true)
  (Prosa_Implementation_Refinements_Refinements_div_of_div_op T
     inst_12 a b)
  (Prosa_Implementation_Refinements_Refinements_add_of_add_op T
     inst_9
     (Prosa_Implementation_Refinements_Refinements_one_of_one_op T
        inst_6)
     (Prosa_Implementation_Refinements_Refinements_div_of_div_op T
        inst_12 a b))
     : forall T : Type,
       Prosa_Implementation_Refinements_Refinements_zero_of T ->
       Prosa_Implementation_Refinements_Refinements_one_of T ->
       Prosa_Implementation_Refinements_Refinements_add_of T ->
       Prosa_Implementation_Refinements_Refinements_div_of T ->
       Prosa_Implementation_Refinements_Refinements_mod_of T ->
       Prosa_Implementation_Refinements_Refinements_eq_of T -> T -> T -> T

Arguments Prosa_Implementation_Refinements_Refinements_div_ceil_T T%_type_scope
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15
  inst_18 
  a b
```
