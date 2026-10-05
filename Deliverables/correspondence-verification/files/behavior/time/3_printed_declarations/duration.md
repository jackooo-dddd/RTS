# `duration`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.time.duration`
- Lean: `Prosa.Behavior.Time.duration`
- Certificate: `duration_relation_total_from_rocq, duration_rocq_roundtrip_certificate, duration_imported_roundtrip_certificate`

## Official Rocq

```coq
duration : Set

duration is not universe polymorphic
duration is transparent
Expands to: Constant prosa.behavior.time.duration
Declared in library prosa.behavior.time, line 7, characters 11-19
duration
     : Set
```

Body:

```coq
duration = nat
     : Set
```

## Lean

```lean
Prosa.Behavior.Time.duration : Type
```

Body:

```lean
@[reducible] def Prosa.Behavior.Time.duration : Type :=
Nat
```

## Lean, imported into Rocq

```coq
Prosa_Behavior_Time_duration
     : Type
```

Body:

```coq
Prosa_Behavior_Time_duration@{} = Nat
     : Type
```
