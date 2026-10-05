# `leb`

- Kind (Rocq): Inductive
- Rocq: `prosa.util.setoid.leb`
- Lean: `Prosa.Util.Setoid.leb`
- Certificate: `leb_constructor_correspondence_certificate`

## Official Rocq

```coq
leb : bool -> bool -> Prop

leb is not universe polymorphic
leb is in Prop but its eliminators are declared dependent by default
Arguments leb (a b)%bool_scope
Expands to: Inductive prosa.util.setoid.leb
Declared in library prosa.util.setoid, line 9, characters 10-13
leb
     : bool -> bool -> Prop
```

## Lean

```lean
Prosa.Util.Setoid.leb : Bool → Bool → Prop
```

## Lean, imported into Rocq

```coq
Prosa_Util_Setoid_leb
     : Bool -> Bool -> SProp
```
