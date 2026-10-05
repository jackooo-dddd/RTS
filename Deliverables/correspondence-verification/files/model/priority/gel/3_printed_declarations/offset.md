# `offset`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.gel.offset`
- Lean: `Prosa.Model.Priority.Gel.offset`
- Certificate: `offset_rocq_roundtrip_certificate, offset_imported_roundtrip_certificate`

## Official Rocq

```coq
offset : Set

offset is not universe polymorphic
offset is transparent
Expands to: Constant prosa.model.priority.gel.offset
Declared in library prosa.model.priority.gel, line 21, characters 11-17
offset
     : Set
```

Body:

```coq
offset = ssrint.int
     : Set
```

## Lean

```lean
Prosa.Model.Priority.Gel.offset : Type
```

Body:

```lean
@[reducible] def Prosa.Model.Priority.Gel.offset : Type :=
ℤ
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Gel_offset
     : Type
```

Body:

```coq
Prosa_Model_Priority_Gel_offset@{} = Int
     : Type
```
