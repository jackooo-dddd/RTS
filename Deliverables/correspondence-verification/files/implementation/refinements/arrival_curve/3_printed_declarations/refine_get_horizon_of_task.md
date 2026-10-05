# `refine_get_horizon_of_task`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_curve.refine_get_horizon_of_task`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.refine_get_horizon_of_task`
- Certificate: `refine_get_horizon_of_task_correspondence`

## Official Rocq

```coq
refine_get_horizon_of_task :
@refines (Equality.sort Task -> nat) (@task_T binnat.N -> binnat.N) (Rtask ==> Rnat) get_horizon_of_task
  (@get_horizon_of_task_T binnat.N one_N)

refine_get_horizon_of_task is not universe polymorphic
refine_get_horizon_of_task is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve.refine_get_horizon_of_task
Declared in library prosa.implementation.refinements.arrival_curve, line 223, characters 18-44
refine_get_horizon_of_task
     : @refines (Equality.sort Task -> nat) (@task_T binnat.N -> binnat.N) (Rtask ==> Rnat)
         get_horizon_of_task (@get_horizon_of_task_T binnat.N one_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.refine_get_horizon_of_task : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    Prosa.Implementation.Refinements.Refinements.Rnat)
  Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task
  Prosa.Implementation.Refinements.Task.get_horizon_of_task_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_refine_get_horizon_of_task
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Task_Task -> Nat)
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Prosa_Implementation_Refinements_Task_Task
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) Nat
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Task_Rtask
            Prosa_Implementation_Refinements_Refinements_Rnat)
         Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task
         (Prosa_Implementation_Refinements_Task_get_horizon_of_task_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_one_N)
```
