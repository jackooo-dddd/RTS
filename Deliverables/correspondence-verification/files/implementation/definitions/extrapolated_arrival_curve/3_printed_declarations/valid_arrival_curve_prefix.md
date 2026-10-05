# `valid_arrival_curve_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix`
- Certificate: `eac_valid_arrival_curve_prefix_correspondence`

## Official Rocq

```coq
valid_arrival_curve_prefix : ArrivalCurvePrefix -> Prop

valid_arrival_curve_prefix is not universe polymorphic
Arguments valid_arrival_curve_prefix ac_prefix
valid_arrival_curve_prefix is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.valid_arrival_curve_prefix
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 113, characters 11-37
valid_arrival_curve_prefix
     : ArrivalCurvePrefix -> Prop
```

Body:

```coq
valid_arrival_curve_prefix =
fun ac_prefix : ArrivalCurvePrefix =>
is_true (positive_horizon ac_prefix) /\
large_horizon ac_prefix /\
is_true (no_inf_arrivals ac_prefix) /\
is_true (specified_bursts ac_prefix) /\ is_true (sorted_ltn_steps ac_prefix)
     : ArrivalCurvePrefix -> Prop

Arguments valid_arrival_curve_prefix ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prop
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prop :=
fun ac_prefix =>
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.positive_horizon ac_prefix = true ∧
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon ac_prefix ∧
      Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.no_inf_arrivals ac_prefix = true ∧
        Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.specified_bursts ac_prefix = true ∧
          Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_ltn_steps ac_prefix = true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> SProp
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
And
  (@eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon ac_prefix) Bool_true)
  (And (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon ac_prefix)
     (And
        (@eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals ac_prefix)
           Bool_true)
        (And
           (@eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_specified_bursts ac_prefix)
              Bool_true)
           (@eq Bool (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps ac_prefix)
              Bool_true))))
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> SProp

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix ac_prefix
```
