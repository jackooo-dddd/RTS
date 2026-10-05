# `ArrivalCurvePrefix`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix`
- Certificate: `eac_prefix_imported_roundtrip`

## Official Rocq

```coq
ArrivalCurvePrefix : Type

ArrivalCurvePrefix is not universe polymorphic
ArrivalCurvePrefix is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.ArrivalCurvePrefix
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 31, characters 11-29
ArrivalCurvePrefix
     : Type
```

Body:

```coq
ArrivalCurvePrefix = (duration * seq (duration * nat))%type
     : Type
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix : Type
```

Body:

```lean
@[reducible] def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix : Type :=
Prosa.Behavior.Time.duration × List (Prosa.Behavior.Time.duration × ℕ)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix
     : Type
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix@{} =
Prod_inst3 Prosa_Behavior_Time_duration (List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat))
     : Type
```
