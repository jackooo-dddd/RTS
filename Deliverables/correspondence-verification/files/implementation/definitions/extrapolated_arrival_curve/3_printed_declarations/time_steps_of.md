# `time_steps_of`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.time_steps_of`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.time_steps_of`
- Certificate: `eac_time_steps_of_correspondence`

## Official Rocq

```coq
time_steps_of : ArrivalCurvePrefix -> seq duration

time_steps_of is not universe polymorphic
Arguments time_steps_of ac_prefix
time_steps_of is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.time_steps_of
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 46, characters 11-24
time_steps_of
     : ArrivalCurvePrefix -> seq duration
```

Body:

```coq
time_steps_of =
fun ac_prefix : ArrivalCurvePrefix => [seq i.1 | i <- steps_of ac_prefix]
     : ArrivalCurvePrefix -> seq duration

Arguments time_steps_of ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.time_steps_of : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  List Prosa.Behavior.Time.duration
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.time_steps_of : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  List Prosa.Behavior.Time.duration :=
fun ac_prefix => List.map Prod.fst (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       List_inst1 Prosa_Behavior_Time_duration
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
List_map_inst3 (Prod_inst3 Prosa_Behavior_Time_duration Nat) Prosa_Behavior_Time_duration
  (Prod_fst_inst3 Prosa_Behavior_Time_duration Nat)
  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of ac_prefix)
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix ->
       List_inst1 Prosa_Behavior_Time_duration

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of ac_prefix
```
