# `specified_bursts`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.specified_bursts`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.specified_bursts`
- Certificate: `eac_specified_bursts_correspondence`

## Official Rocq

```coq
specified_bursts : ArrivalCurvePrefix -> bool

specified_bursts is not universe polymorphic
Arguments specified_bursts ac_prefix
specified_bursts is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.specified_bursts
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 103, characters 11-27
specified_bursts
     : ArrivalCurvePrefix -> bool
```

Body:

```coq
specified_bursts =
fun ac_prefix : ArrivalCurvePrefix => 1 \in time_steps_of ac_prefix
     : ArrivalCurvePrefix -> bool

Arguments specified_bursts ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.specified_bursts : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.specified_bursts : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool :=
fun ac_prefix => decide (1 ∈ Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.time_steps_of ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_specified_bursts
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_specified_bursts@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
Decidable_decide
  (Membership_mem_inst3 Prosa_Behavior_Time_duration (List_inst1 Prosa_Behavior_Time_duration)
     (List_instMembership_inst1 Prosa_Behavior_Time_duration)
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of ac_prefix)
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
  (List_instDecidableMemOfLawfulBEq_inst1 Prosa_Behavior_Time_duration
     (instBEqOfDecidableEq_inst1 Prosa_Behavior_Time_duration instDecidableEqNat) Nat_instLawfulBEq
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of ac_prefix))
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_specified_bursts ac_prefix
```
