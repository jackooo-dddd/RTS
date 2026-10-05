# `set`

- Kind (Rocq): Record
- Rocq: `prosa.util.seqset.set`
- Lean: `Prosa.Util.Seqset.set`
- Certificate: `seqset_set_correspondence_certificate`

## Official Rocq

```coq
set : eqType -> Type

set is not universe polymorphic
Arguments set {T}
Expands to: Inductive prosa.util.seqset.set
Declared in library prosa.util.seqset, line 12, characters 9-12
@set
     : eqType -> Type
```

## Lean

```lean
Prosa.Util.Seqset.set : (T : Type u_1) → [DecidableEq T] → Type u_1
```

## Lean, imported into Rocq

```coq
Prosa_Util_Seqset_set
     : forall T : Type, DecidableEq T -> Type
```
