# `horizon_of`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.horizon_of`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of`
- Certificate: `eac_horizon_of_correspondence`

## Official Rocq

```coq
horizon_of : ArrivalCurvePrefix -> duration

horizon_of is not universe polymorphic
Arguments horizon_of ac_prefix
horizon_of is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.horizon_of
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 38, characters 11-21
horizon_of
     : ArrivalCurvePrefix -> duration
```

Body:

```coq
horizon_of = [eta @fst duration (seq (duration * nat))]
     : ArrivalCurvePrefix -> duration

Arguments horizon_of ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prosa.Behavior.Time.duration :=
fun ac_prefix => ac_prefix.1
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
Prod_fst_inst3 Prosa_Behavior_Time_duration (List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat))
  ac_prefix
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       Prosa_Behavior_Time_duration

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix
```
