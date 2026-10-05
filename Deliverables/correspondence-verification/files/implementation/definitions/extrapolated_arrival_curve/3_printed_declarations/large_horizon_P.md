# `large_horizon_P`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_P`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon_P`
- Certificate: `eac_large_horizon_P_statement_correspondence`

## Official Rocq

```coq
large_horizon_P :
forall ac_prefix : ArrivalCurvePrefix, reflect (large_horizon ac_prefix) (large_horizon_dec ac_prefix)

large_horizon_P is not universe polymorphic
Arguments large_horizon_P ac_prefix
large_horizon_P is opaque
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_P
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 87, characters 6-21
large_horizon_P
     : forall ac_prefix : ArrivalCurvePrefix, reflect (large_horizon ac_prefix) (large_horizon_dec ac_prefix)
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon_P : (ac_prefix :
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix) →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.BoolReflect
    (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon ac_prefix)
    (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon_dec ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_P
     : forall ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix,
       Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon ac_prefix)
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_dec ac_prefix)
```
