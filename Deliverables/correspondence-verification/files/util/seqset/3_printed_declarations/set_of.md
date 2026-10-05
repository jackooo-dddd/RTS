# `set_of`

- Kind (Rocq): Definition
- Rocq: `prosa.util.seqset.set_of`
- Lean: `Prosa.Util.Seqset.set_of`
- Certificate: `seqset_set_of_correspondence_certificate`

## Official Rocq

```coq
set_of : forall {T : eqType}, phant (Equality.sort T) -> Type

set_of is not universe polymorphic
Arguments set_of {T} _
set_of is transparent
Expands to: Constant prosa.util.seqset.set_of
Declared in library prosa.util.seqset, line 24, characters 13-19
@set_of
     : forall T : eqType, phant (Equality.sort T) -> Type
```

Body:

```coq
set_of = fun T : eqType => fun=> @set T
     : forall {T : eqType}, phant (Equality.sort T) -> Type

Arguments set_of {T} _
```

## Lean

```lean
Prosa.Util.Seqset.set_of : (T : Type u_1) → [DecidableEq T] → Type u_1
@[reducible] def Prosa.Util.Seqset.set_of.{u} : (T : Type u) → [DecidableEq T] → Type u :=
fun T [DecidableEq T] => Prosa.Util.Seqset.set T
```

## Lean, imported into Rocq

```coq
Prosa_Util_Seqset_set_of
     : forall T : Type, DecidableEq T -> Type
```

Body:

```coq
Prosa_Util_Seqset_set_of@{u Lean.u+1.0 Lean.u+2.0} =
fun (T : Type) (inst_3 : DecidableEq T) =>
Prosa_Util_Seqset_set T inst_3
     : forall T : Type, DecidableEq T -> Type

Arguments Prosa_Util_Seqset_set_of T%_type_scope inst_3
```
