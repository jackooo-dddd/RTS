# `refine_task_arrival`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.task.refine_task_arrival`
- Lean: `Prosa.Implementation.Refinements.Task.refine_task_arrival`
- Certificate: `refine_task_arrival_correspondence`

## Official Rocq

```coq
refine_task_arrival :
@refines (Equality.sort Task -> task_arrivals_bound) (@task_T binnat.N -> @task_arrivals_bound_T binnat.N)
  (Rtask ==> Rtask_ab) task_arrival (@task_arrival_T binnat.N)

refine_task_arrival is not universe polymorphic
refine_task_arrival is opaque
Expands to: Constant prosa.implementation.refinements.task.refine_task_arrival
Declared in library prosa.implementation.refinements.task, line 167, characters 18-37
refine_task_arrival
     : @refines (Equality.sort Task -> task_arrivals_bound)
         (@task_T binnat.N -> @task_arrivals_bound_T binnat.N) (Rtask ==> Rtask_ab) task_arrival
         (@task_arrival_T binnat.N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.refine_task_arrival : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab)
  Prosa.Implementation.Definitions.Task.concrete_task.task_arrival
  Prosa.Implementation.Refinements.Task.task_T.task_arrival_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_refine_task_arrival
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Task_Task ->
          Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound)
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
            Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Prosa_Implementation_Refinements_Task_Task
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound
            (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
               Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Refinements_Task_Rtask
            Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab)
         Prosa_Implementation_Definitions_Task_concrete_task_task_arrival
         (Prosa_Implementation_Refinements_Task_task_T_task_arrival_T
            Prosa_Implementation_Refinements_Refinements_N)
```
