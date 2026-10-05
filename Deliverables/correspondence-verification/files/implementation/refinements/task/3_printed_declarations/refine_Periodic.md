# `refine_Periodic`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.task.refine_Periodic`
- Lean: `Prosa.Implementation.Refinements.Task.refine_Periodic`
- Certificate: `refine_Periodic_correspondence`

## Official Rocq

```coq
refine_Periodic :
@refines (nat -> task_arrivals_bound) (binnat.N -> @task_arrivals_bound_T binnat.N) 
  (Rnat ==> Rtask_ab) Periodic (@Periodic_T binnat.N)

refine_Periodic is not universe polymorphic
refine_Periodic is opaque
Expands to: Constant prosa.implementation.refinements.task.refine_Periodic
Declared in library prosa.implementation.refinements.task, line 191, characters 18-33
refine_Periodic
     : @refines (nat -> task_arrivals_bound) (binnat.N -> @task_arrivals_bound_T binnat.N)
         (Rnat ==> Rtask_ab) Periodic (@Periodic_T binnat.N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.refine_Periodic : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
    Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab)
  Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Periodic
  Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Periodic_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_refine_Periodic
     : Prosa_Implementation_Refinements_Refinements_refines
         (Nat -> Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound)
         (Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
            Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound
            (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
               Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Refinements_Refinements_Rnat
            Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab)
         Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
         (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Periodic_T
            Prosa_Implementation_Refinements_Refinements_N)
```
