# `instant`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.time.instant`
- Lean: `Prosa.Behavior.Time.instant`
- Certificate: `instant_relation_total_from_rocq, instant_rocq_roundtrip_certificate, instant_imported_roundtrip_certificate`

## Official Rocq

```coq
instant : Set

instant is not universe polymorphic
instant is transparent
Expands to: Constant prosa.behavior.time.instant
Declared in library prosa.behavior.time, line 8, characters 11-18
instant
     : Set
```

Body:

```coq
instant = nat
     : Set
```

## Lean

```lean
Prosa.Behavior.Time.instant : Type
```

Body:

```lean
@[reducible] def Prosa.Behavior.Time.instant : Type :=
Nat
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Time_instant
     : Type
```

Body:

```coq
Prosa_Behavior_Time_instant@{} = Nat
     : Type
```
