# `valid_arrival_curve_prefix_P`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_P`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix_P`
- Certificate: `eac_valid_arrival_curve_prefix_P_statement_correspondence`

## Official Rocq

```coq
valid_arrival_curve_prefix_P :
forall ac_prefix : ArrivalCurvePrefix,
reflect (valid_arrival_curve_prefix ac_prefix) (valid_arrival_curve_prefix_dec ac_prefix)

valid_arrival_curve_prefix_P is not universe polymorphic
Arguments valid_arrival_curve_prefix_P ac_prefix
valid_arrival_curve_prefix_P is opaque
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_P
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 129, characters 6-34
valid_arrival_curve_prefix_P
     : forall ac_prefix : ArrivalCurvePrefix,
       reflect (valid_arrival_curve_prefix ac_prefix) (valid_arrival_curve_prefix_dec ac_prefix)
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix_P : (ac_prefix :
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix) →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.BoolReflect
    (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix ac_prefix)
    (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix_dec ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_P
     : forall ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix,
       Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix ac_prefix)
         (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec ac_prefix)
```
