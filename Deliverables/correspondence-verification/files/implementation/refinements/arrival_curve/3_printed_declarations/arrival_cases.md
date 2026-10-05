# `arrival_cases`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.arrival_curve.arrival_cases`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.arrival_cases`
- Certificate: `arrival_cases_correspondence`

## Official Rocq

```coq
arrival_cases :
forall tsk : Equality.sort Task,
is_periodic_arrivals tsk \/ is_sporadic_arrivals tsk \/ is_etamax_arrivals tsk

arrival_cases is not universe polymorphic
Arguments arrival_cases tsk
arrival_cases is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve.arrival_cases
Declared in library prosa.implementation.refinements.arrival_curve, line 74, characters 8-21
arrival_cases
     : forall tsk : Equality.sort Task,
       is_periodic_arrivals tsk \/ is_sporadic_arrivals tsk \/ is_etamax_arrivals tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.arrival_cases : ∀ (tsk : Prosa.Implementation.Refinements.Task.Task),
  Prosa.Implementation.Refinements.ArrivalCurve.is_periodic_arrivals tsk ∨
    Prosa.Implementation.Refinements.ArrivalCurve.is_sporadic_arrivals tsk ∨
      Prosa.Implementation.Refinements.ArrivalCurve.is_etamax_arrivals tsk
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_arrival_cases
     : forall tsk : Prosa_Implementation_Refinements_Task_Task,
       Or (Prosa_Implementation_Refinements_ArrivalCurve_is_periodic_arrivals tsk)
         (Or (Prosa_Implementation_Refinements_ArrivalCurve_is_sporadic_arrivals tsk)
            (Prosa_Implementation_Refinements_ArrivalCurve_is_etamax_arrivals tsk))
```
