# `is_etamax_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_curve.is_etamax_arrivals`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.is_etamax_arrivals`
- Certificate: `is_etamax_arrivals_correspondence`

## Official Rocq

```coq
is_etamax_arrivals : Equality.sort Task -> Prop

is_etamax_arrivals is not universe polymorphic
Arguments is_etamax_arrivals tsk
is_etamax_arrivals is transparent
Expands to: Constant prosa.implementation.refinements.arrival_curve.is_etamax_arrivals
Declared in library prosa.implementation.refinements.arrival_curve, line 50, characters 11-29
is_etamax_arrivals
     : Equality.sort Task -> Prop
```

Body:

```coq
is_etamax_arrivals =
fun tsk : Equality.sort Task =>
exists ac_prefix_vec : ArrivalCurvePrefix, task_arrival tsk = ArrivalPrefix ac_prefix_vec
     : Equality.sort Task -> Prop

Arguments is_etamax_arrivals tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.is_etamax_arrivals : Prosa.Implementation.Refinements.Task.Task → Prop
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalCurve.is_etamax_arrivals : Prosa.Implementation.Refinements.Task.Task →
  Prop :=
fun tsk =>
  ∃ ac_prefix_vec,
    tsk.task_arrival = Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.ArrivalPrefix ac_prefix_vec
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_is_etamax_arrivals
     : Prosa_Implementation_Refinements_Task_Task -> SProp
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalCurve_is_etamax_arrivals@{} =
fun tsk : Prosa_Implementation_Refinements_Task_Task =>
Exists Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix
  (fun ac_prefix_vec : Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix =>
   Prosa_Implementation_Definitions_Task_concrete_task_task_arrival tsk =
   Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix ac_prefix_vec)
     : Prosa_Implementation_Refinements_Task_Task -> SProp

Arguments Prosa_Implementation_Refinements_ArrivalCurve_is_etamax_arrivals tsk
```
