# `value_at`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.value_at`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at`
- Certificate: `eac_value_at_correspondence`

## Official Rocq

```coq
value_at : ArrivalCurvePrefix -> duration -> nat

value_at is not universe polymorphic
Arguments value_at ac_prefix t
value_at is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.value_at
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 56, characters 11-19
value_at
     : ArrivalCurvePrefix -> duration -> nat
```

Body:

```coq
value_at =
fun (ac_prefix : ArrivalCurvePrefix) (t : duration) => (step_at ac_prefix t).2
     : ArrivalCurvePrefix -> duration -> nat

Arguments value_at ac_prefix t
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Behavior.Time.duration → ℕ :=
fun ac_prefix t => (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.step_at ac_prefix t).2
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at@{} =
fun (ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix)
  (t : Prosa_Behavior_Time_duration) =>
Prod_snd_inst3 Prosa_Behavior_Time_duration Nat
  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at ac_prefix t)
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at ac_prefix t
```
