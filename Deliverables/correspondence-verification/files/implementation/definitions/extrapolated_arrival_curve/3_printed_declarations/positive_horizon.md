# `positive_horizon`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.positive_horizon`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.positive_horizon`
- Certificate: `eac_positive_horizon_correspondence`

## Official Rocq

```coq
positive_horizon : ArrivalCurvePrefix -> bool

positive_horizon is not universe polymorphic
Arguments positive_horizon ac_prefix
positive_horizon is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.positive_horizon
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 75, characters 11-27
positive_horizon
     : ArrivalCurvePrefix -> bool
```

Body:

```coq
positive_horizon =
fun ac_prefix : ArrivalCurvePrefix => 0 < horizon_of ac_prefix
     : ArrivalCurvePrefix -> bool

Arguments positive_horizon ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.positive_horizon : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.positive_horizon : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool :=
fun ac_prefix => decide (0 < Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
Decidable_decide
  (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix))
  (Nat_decLt (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix))
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon ac_prefix
```
