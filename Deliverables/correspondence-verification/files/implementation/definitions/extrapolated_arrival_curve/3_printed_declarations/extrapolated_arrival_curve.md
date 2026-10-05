# `extrapolated_arrival_curve`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.extrapolated_arrival_curve`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve`
- Certificate: `eac_extrapolated_arrival_curve_correspondence`

## Official Rocq

```coq
extrapolated_arrival_curve : ArrivalCurvePrefix -> duration -> nat

extrapolated_arrival_curve is not universe polymorphic
Arguments extrapolated_arrival_curve ac_prefix t
extrapolated_arrival_curve is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.extrapolated_arrival_curve
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 68, characters 11-37
extrapolated_arrival_curve
     : ArrivalCurvePrefix -> duration -> nat
```

Body:

```coq
extrapolated_arrival_curve =
fun (ac_prefix : ArrivalCurvePrefix) (t : duration) =>
let h := horizon_of ac_prefix in t %/ h * value_at ac_prefix h + value_at ac_prefix (t %% h)
     : ArrivalCurvePrefix -> duration -> nat

Arguments extrapolated_arrival_curve ac_prefix t
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Behavior.Time.duration → ℕ :=
fun ac_prefix t =>
  have h := Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix;
  t / h * Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at ac_prefix h +
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at ac_prefix (t % h)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve@{} =
fun (ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix)
  (t : Prosa_Behavior_Time_duration) =>
let h := Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix in
HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
  (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
  (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
     (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
     (HDiv_hDiv_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
        (instHDiv_inst1 Prosa_Behavior_Time_duration Nat_instDiv) t h)
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix h))
  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix
     (HMod_hMod_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
        (instHMod_inst1 Prosa_Behavior_Time_duration Nat_instMod) t h))
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve ac_prefix t
```
