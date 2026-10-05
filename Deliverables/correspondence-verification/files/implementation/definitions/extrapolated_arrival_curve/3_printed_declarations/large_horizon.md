# `large_horizon`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon`
- Certificate: `eac_large_horizon_correspondence`

## Official Rocq

```coq
large_horizon : ArrivalCurvePrefix -> Prop

large_horizon is not universe polymorphic
Arguments large_horizon ac_prefix
large_horizon is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.large_horizon
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 79, characters 11-24
large_horizon
     : ArrivalCurvePrefix -> Prop
```

Body:

```coq
large_horizon =
fun ac_prefix : ArrivalCurvePrefix =>
forall s : Equality.sort Datatypes_nat__canonical__eqtype_Equality,
is_true (s \in time_steps_of ac_prefix) -> is_true (s <= horizon_of ac_prefix)
     : ArrivalCurvePrefix -> Prop

Arguments large_horizon ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prop
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Prop :=
fun ac_prefix =>
  ∀ s ∈ Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.time_steps_of ac_prefix,
    s ≤ Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of ac_prefix
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> SProp
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
forall s : Prosa_Behavior_Time_duration,
Membership_mem_inst3 Prosa_Behavior_Time_duration (List_inst1 Prosa_Behavior_Time_duration)
  (List_instMembership_inst1 Prosa_Behavior_Time_duration)
  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of ac_prefix) s ->
LE_le_inst1 Prosa_Behavior_Time_duration instLENat s
  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of ac_prefix)
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> SProp

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_large_horizon ac_prefix
```
