# `eqn_task_arrivals_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.definitions.arrival_bound.eqn_task_arrivals_bound`
- Lean: `Prosa.Implementation.Definitions.ArrivalBound.eqn_task_arrivals_bound`
- Certificate: `ab_eqn_task_arrivals_bound_statement_correspondence`

## Official Rocq

```coq
eqn_task_arrivals_bound : Equality.axiom (T:=task_arrivals_bound) task_arrivals_bound_eqdef

eqn_task_arrivals_bound is not universe polymorphic
Arguments eqn_task_arrivals_bound x y
eqn_task_arrivals_bound is opaque
Expands to: Constant prosa.implementation.definitions.arrival_bound.eqn_task_arrivals_bound
Declared in library prosa.implementation.definitions.arrival_bound, line 33, characters 6-29
eqn_task_arrivals_bound
     : Equality.axiom (T:=task_arrivals_bound) task_arrivals_bound_eqdef
```

## Lean

```lean
Prosa.Implementation.Definitions.ArrivalBound.eqn_task_arrivals_bound : (x y :
    Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound) →
  Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.BoolReflect (x = y)
    (Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound_eqdef x y)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Definitions_ArrivalBound_eqn_task_arrivals_bound
     : forall x y : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound,
       Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_BoolReflect
         (@eq Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound x y)
         (Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_eqdef x y)
```
