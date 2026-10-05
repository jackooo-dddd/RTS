# `steps_of`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.steps_of`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of`
- Certificate: `eac_steps_of_correspondence`

## Official Rocq

```coq
steps_of : ArrivalCurvePrefix -> seq (duration * nat)

steps_of is not universe polymorphic
Arguments steps_of ac_prefix
steps_of is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.steps_of
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 41, characters 11-19
steps_of
     : ArrivalCurvePrefix -> seq (duration * nat)
```

Body:

```coq
steps_of = [eta @snd duration (seq (duration * nat))]
     : ArrivalCurvePrefix -> seq (duration * nat)

Arguments steps_of ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  List (Prosa.Behavior.Time.duration × ℕ)
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  List (Prosa.Behavior.Time.duration × ℕ) :=
fun ac_prefix => ac_prefix.2
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
Prod_snd_inst3 Prosa_Behavior_Time_duration (List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat))
  ac_prefix
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       List_inst1 (Prod_inst3 Prosa_Behavior_Time_duration Nat)

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of ac_prefix
```
