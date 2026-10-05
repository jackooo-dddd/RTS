# `valid_arrival_curve_prefix_dec`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_dec`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix_dec`
- Certificate: `eac_valid_arrival_curve_prefix_dec_correspondence`

## Official Rocq

```coq
valid_arrival_curve_prefix_dec : ArrivalCurvePrefix -> bool

valid_arrival_curve_prefix_dec is not universe polymorphic
Arguments valid_arrival_curve_prefix_dec ac_prefix
valid_arrival_curve_prefix_dec is transparent
Expands to: Constant
            prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix_dec
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 121, characters 11-41
valid_arrival_curve_prefix_dec
     : ArrivalCurvePrefix -> bool
```

Body:

```coq
valid_arrival_curve_prefix_dec =
fun ac_prefix : ArrivalCurvePrefix =>
positive_horizon ac_prefix && large_horizon_dec ac_prefix && no_inf_arrivals ac_prefix &&
specified_bursts ac_prefix && sorted_ltn_steps ac_prefix
     : ArrivalCurvePrefix -> bool

Arguments valid_arrival_curve_prefix_dec ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix_dec : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix_dec : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool :=
fun ac_prefix =>
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.positive_horizon ac_prefix &&
          Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon_dec ac_prefix &&
        Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.no_inf_arrivals ac_prefix &&
      Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.specified_bursts ac_prefix &&
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_ltn_steps ac_prefix
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
Bool_and
  (Bool_and
     (Bool_and
        (Bool_and (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon ac_prefix)
           (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_dec ac_prefix))
        (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals ac_prefix))
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_specified_bursts ac_prefix))
  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps ac_prefix)
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix_dec ac_prefix
```
