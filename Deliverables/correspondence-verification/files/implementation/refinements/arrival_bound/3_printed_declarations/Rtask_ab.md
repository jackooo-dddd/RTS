# `Rtask_ab`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.arrival_bound.Rtask_ab`
- Lean: `Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab`
- Certificate: `Rtask_ab_correspondence`

## Official Rocq

```coq
Rtask_ab : task_arrivals_bound -> @task_arrivals_bound_T N -> Type

Rtask_ab is not universe polymorphic
Rtask_ab is transparent
Expands to: Constant prosa.implementation.refinements.arrival_bound.Rtask_ab
Declared in library prosa.implementation.refinements.arrival_bound, line 129, characters 11-19
Rtask_ab
     : task_arrivals_bound -> @task_arrivals_bound_T N -> Type
```

Body:

```coq
Rtask_ab =
@fun_hrel task_arrivals_bound (@task_arrivals_bound_T N) task_abT_to_task_ab
     : task_arrivals_bound -> @task_arrivals_bound_T N -> Type
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab : Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound →
  Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T Prosa.Implementation.Refinements.Refinements.N →
    Type
```

Body:

```lean
def Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab : Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound →
  Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T Prosa.Implementation.Refinements.Refinements.N →
    Type :=
Prosa.Implementation.Refinements.Refinements.fun_hrel Prosa.Implementation.Refinements.ArrivalBound.task_abT_to_task_ab
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab
     : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
       Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
         Prosa_Implementation_Refinements_Refinements_N ->
       Type
```

Body:

```coq
Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab@{} =
Prosa_Implementation_Refinements_Refinements_fun_hrel
  Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound
  (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
     Prosa_Implementation_Refinements_Refinements_N)
  Prosa_Implementation_Refinements_ArrivalBound_task_abT_to_task_ab
     : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
       Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
         Prosa_Implementation_Refinements_Refinements_N ->
       Type

Arguments Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab a____at____internal__hyg0
  a____at____internal__hyg0
```
