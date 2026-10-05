# `has_valid_arrival_curve_prefix`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.has_valid_arrival_curve_prefix`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.has_valid_arrival_curve_prefix`
- Certificate: `has_valid_arrival_curve_prefix_correspondence`

## Official Rocq

```coq
has_valid_arrival_curve_prefix : Equality.sort Task -> Prop

has_valid_arrival_curve_prefix is not universe polymorphic
Arguments has_valid_arrival_curve_prefix tsk
has_valid_arrival_curve_prefix is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.has_valid_arrival_curve_prefix
Declared in library prosa.implementation.refinements.arrival_curve, line 55, characters 11-41
has_valid_arrival_curve_prefix
     : Equality.sort Task -> Prop
```

Body:

```coq
has_valid_arrival_curve_prefix =
fun tsk : Equality.sort Task =>
exists ac_prefix_vec : ArrivalCurvePrefix,
  get_arrival_curve_prefix tsk = ac_prefix_vec /\ valid_arrival_curve_prefix ac_prefix_vec
     : Equality.sort Task -> Prop

Arguments has_valid_arrival_curve_prefix tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.has_valid_arrival_curve_prefix : Prosa.Implementation.Refinements.Task.Task →
  Prop
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.has_valid_arrival_curve_prefix : Prosa.Implementation.Refinements.Task.Task →
  Prop :=
fun tsk =>
  ∃ ac_prefix_vec,
    Prosa.Implementation.Definitions.Task.get_arrival_curve_prefix tsk = ac_prefix_vec ∧
      Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix ac_prefix_vec
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_has_valid_arrival_curve_prefix
     : Prosa_Implementation_Refinements_Task_Task -> SProp
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_has_valid_arrival_curve_prefix@{} =
fun tsk : Prosa_Implementation_Refinements_Task_Task =>
Exists Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix
  (fun ac_prefix_vec : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
   And
     (@eq Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix
        (Prosa_Implementation_Definitions_Task_get_arrival_curve_prefix tsk) ac_prefix_vec)
     (Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_valid_arrival_curve_prefix ac_prefix_vec))
     : Prosa_Implementation_Refinements_Task_Task -> SProp

Arguments Prosa_Implementation_Refinements_ArrivalCurve_has_valid_arrival_curve_prefix tsk
```
