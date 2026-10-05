# `refine_Sporadic`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.task.refine_Sporadic`
- Lean: `Prosa.Implementation.Refinements.Task.refine_Sporadic`
- Certificate: `refine_Sporadic_correspondence`

## Official Rocq

```coq
refine_Sporadic :
@refines (nat -> task_arrivals_bound) (binnat.N -> @task_arrivals_bound_T binnat.N) 
  (Rnat ==> Rtask_ab) Sporadic (@Sporadic_T binnat.N)

refine_Sporadic is not universe polymorphic
refine_Sporadic is opaque
Expands to: Constant prosa.implementation.refinements.task.refine_Sporadic
Declared in library prosa.implementation.refinements.task, line 200, characters 18-33
refine_Sporadic
     : @refines (nat -> task_arrivals_bound) (binnat.N -> @task_arrivals_bound_T binnat.N)
         (Rnat ==> Rtask_ab) Sporadic (@Sporadic_T binnat.N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.refine_Sporadic : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
    Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab)
  Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound.Sporadic
  Prosa.Implementation.Refinements.ArrivalBound.task_arrivals_bound_T.Sporadic_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_refine_Sporadic
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
         Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
         (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T_Sporadic_T
            Prosa_Implementation_Refinements_Refinements_N)
```
