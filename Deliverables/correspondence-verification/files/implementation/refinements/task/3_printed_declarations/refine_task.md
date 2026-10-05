# `refine_task`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.task.refine_task`
- Lean: `Prosa.Implementation.Refinements.Task.refine_task`
- Certificate: `refine_task_correspondence`

## Official Rocq

```coq
refine_task :
@refines (nat -> nat -> task_arrivals_bound -> nat -> nat -> Equality.sort Task)
  (binnat.N -> binnat.N -> @task_arrivals_bound_T binnat.N -> binnat.N -> binnat.N -> @task_T binnat.N)
  (Rnat ==> Rnat ==> Rtask_ab ==> Rnat ==> Rnat ==> Rtask) Build_concrete_task (@Build_task_T binnat.N)

refine_task is not universe polymorphic
refine_task is opaque
Expands to: Constant prosa.implementation.refinements.task.refine_task
Declared in library prosa.implementation.refinements.task, line 143, characters 18-29
refine_task
     : @refines (nat -> nat -> task_arrivals_bound -> nat -> nat -> Equality.sort Task)
         (binnat.N -> binnat.N -> @task_arrivals_bound_T binnat.N -> binnat.N -> binnat.N -> @task_T binnat.N)
         (Rnat ==> Rnat ==> Rtask_ab ==> Rnat ==> Rnat ==> Rtask) Build_concrete_task
         (@Build_task_T binnat.N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.refine_task : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.ArrivalBound.Rtask_ab
        (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
          (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
            Prosa.Implementation.Refinements.Task.Rtask)))))
  Prosa.Implementation.Definitions.Task.concrete_task.mk Prosa.Implementation.Refinements.Task.task_T.mk
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_refine_task
     : Prosa_Implementation_Refinements_Refinements_refines
         (Nat ->
          Nat ->
          Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
          Nat -> Nat -> Prosa_Implementation_Refinements_Task_Task)
         (Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
            Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N
            (Nat ->
             Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
             Nat -> Nat -> Prosa_Implementation_Refinements_Task_Task)
            (Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
               Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Refinements_Refinements_Rnat
            (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
               Prosa_Implementation_Refinements_Refinements_N
               (Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound ->
                Nat -> Nat -> Prosa_Implementation_Refinements_Task_Task)
               (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
                  Prosa_Implementation_Refinements_Refinements_N ->
                Prosa_Implementation_Refinements_Refinements_N ->
                Prosa_Implementation_Refinements_Refinements_N ->
                Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Refinements_Rnat
               (Prosa_Implementation_Refinements_Refinements_hrespectful
                  Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound
                  (Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
                     Prosa_Implementation_Refinements_Refinements_N)
                  (Nat -> Nat -> Prosa_Implementation_Refinements_Task_Task)
                  (Prosa_Implementation_Refinements_Refinements_N ->
                   Prosa_Implementation_Refinements_Refinements_N ->
                   Prosa_Implementation_Refinements_Task_task_T
                     Prosa_Implementation_Refinements_Refinements_N)
                  Prosa_Implementation_Refinements_ArrivalBound_Rtask_ab
                  (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
                     Prosa_Implementation_Refinements_Refinements_N
                     (Nat -> Prosa_Implementation_Refinements_Task_Task)
                     (Prosa_Implementation_Refinements_Refinements_N ->
                      Prosa_Implementation_Refinements_Task_task_T
                        Prosa_Implementation_Refinements_Refinements_N)
                     Prosa_Implementation_Refinements_Refinements_Rnat
                     (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
                        Prosa_Implementation_Refinements_Refinements_N
                        Prosa_Implementation_Refinements_Task_Task
                        (Prosa_Implementation_Refinements_Task_task_T
                           Prosa_Implementation_Refinements_Refinements_N)
                        Prosa_Implementation_Refinements_Refinements_Rnat
                        Prosa_Implementation_Refinements_Task_Rtask)))))
         Prosa_Implementation_Definitions_Task_concrete_task_mk
         (Prosa_Implementation_Refinements_Task_task_T_mk Prosa_Implementation_Refinements_Refinements_N)
```
