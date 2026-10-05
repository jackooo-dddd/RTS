# `constant`

- Kind (Rocq): Definition
- Rocq: `prosa.util.notation.constant`
- Lean: `Prosa.Util.Notation.constant`
- Certificate: `constant_value_certificate`

## Official Rocq

```coq
constant : forall {X Y : Type}, Y -> X -> Y

constant is not universe polymorphic
Arguments constant {X Y}%type_scope c _
constant is transparent
Expands to: Constant prosa.util.notation.constant
Declared in library prosa.util.notation, line 5, characters 11-19
@constant
     : forall X Y : Type, Y -> X -> Y
```

Body:

```coq
constant = fun (X Y : Type) (c : Y) => fun=> c
     : forall {X Y : Type}, Y -> X -> Y

Arguments constant {X Y}%type_scope c _
```

## Lean

```lean
@Prosa.Util.Notation.constant : {X : Type u_1} → {Y : Type u_2} → Y → X → Y
def Prosa.Util.Notation.constant.{u, v} : {X : Type u} → {Y : Type v} → Y → X → Y :=
fun {X} {Y} c x => c
```

## Lean, imported into Rocq

```coq
Prosa_Util_Notation_constant
     : forall X Y : Type, Y -> X -> Y
```

Body:

```coq
Prosa_Util_Notation_constant@{u v Lean.u+1.0 Lean.v+1.0} =
fun (X Y : Type) (c : Y) (_ : X) => c
     : forall X Y : Type, Y -> X -> Y

Arguments Prosa_Util_Notation_constant (X Y)%_type_scope c a____at____internal__hyg0
```
