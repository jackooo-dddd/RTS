# `sorted_ltn_steps`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.definitions.extrapolated_arrival_curve.sorted_ltn_steps`
- Lean: `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_ltn_steps`
- Certificate: `eac_sorted_ltn_steps_correspondence`

## Official Rocq

```coq
sorted_ltn_steps : ArrivalCurvePrefix -> bool

sorted_ltn_steps is not universe polymorphic
Arguments sorted_ltn_steps ac_prefix
sorted_ltn_steps is transparent
Expands to: Constant prosa.implementation.definitions.extrapolated_arrival_curve.sorted_ltn_steps
Declared in library prosa.implementation.definitions.extrapolated_arrival_curve, line 108, characters 11-27
sorted_ltn_steps
     : ArrivalCurvePrefix -> bool
```

Body:

```coq
sorted_ltn_steps =
fun ac_prefix : ArrivalCurvePrefix => @sorted (nat * nat) ltn_steps (steps_of ac_prefix)
     : ArrivalCurvePrefix -> bool

Arguments sorted_ltn_steps ac_prefix
```

## Lean

```lean
Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_ltn_steps : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool
```

Body:

```lean
def Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_ltn_steps : Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix →
  Bool :=
fun ac_prefix =>
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sortedBool
    Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ltn_steps
    (Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of ac_prefix)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool
```

Body:

```coq
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps@{} =
fun ac_prefix : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sortedBool_inst1
  (Prod_inst3 Prosa_Behavior_Time_duration Nat)
  Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps
  (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of ac_prefix)
     : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix -> Bool

Arguments Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps ac_prefix
```
