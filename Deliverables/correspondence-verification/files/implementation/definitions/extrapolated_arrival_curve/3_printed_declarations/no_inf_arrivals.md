# `no_inf_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.no_inf_arrivals`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.no_inf_arrivals`
- Certificate: `eac_no_inf_arrivals_correspondence`

## Official Rocq

```coq
no_inf_arrivals : ArrivalCurvePrefix -> bool

no_inf_arrivals is not universe polymorphic
Arguments no_inf_arrivals ac_prefix
no_inf_arrivals is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.no_inf_arrivals
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 98, characters 11-26
no_inf_arrivals
     : ArrivalCurvePrefix -> bool
```

Body:

```coq
no_inf_arrivals =
fun ac_prefix : ArrivalCurvePrefix => value_at ac_prefix 0 == 0
     : ArrivalCurvePrefix -> bool

Arguments no_inf_arrivals ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.no_inf_arrivals : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.no_inf_arrivals : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool :=
fun ac_prefix => decide (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at ac_prefix 0 = 0)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
Decidable_decide
  (@eq Nat
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix
        (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
     (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
  (instDecidableEqNat
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix
        (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
     (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals ac_prefix
```
