# `large_horizon_dec`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_dec`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon_dec`
- Certificate: `eac_large_horizon_dec_correspondence`

## Official Rocq

```coq
large_horizon_dec : ArrivalCurvePrefix -> bool

large_horizon_dec is not universe polymorphic
Arguments large_horizon_dec ac_prefix
large_horizon_dec is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon_dec
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 83, characters 11-28
large_horizon_dec
     : ArrivalCurvePrefix -> bool
```

Body:

```coq
large_horizon_dec =
fun ac_prefix : ArrivalCurvePrefix => @all nat (leq^~ (horizon_of ac_prefix)) (time_steps_of ac_prefix)
     : ArrivalCurvePrefix -> bool

Arguments large_horizon_dec ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon_dec : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon_dec : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool :=
fun ac_prefix =>
  (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.time_steps_of ac_prefix).all fun s =>
    decide (s ≤ Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_dec
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_dec@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
List_all_inst1 Prosa_Behavior_Time_duration
  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of ac_prefix)
  (fun s : Prosa_Behavior_Time_duration =>
   Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_duration instLENat s
        (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix))
     (Nat_decLe s (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix)))
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon_dec ac_prefix
```
