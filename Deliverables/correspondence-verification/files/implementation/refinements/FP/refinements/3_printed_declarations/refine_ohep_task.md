# `refine_ohep_task`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.refine_ohep_task`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.refine_ohep_task`
- Certificate: `refine_ohep_task_correspondence`

## Official Rocq

```coq
refine_ohep_task :
@refines (Equality.sort Task -> Equality.sort Task -> bool) (@task_T N -> @task_T N -> bool)
  (Rtask ==> Rtask ==> bool_R) ohep_task (@ohep_task_T N leq_N eq_task)

refine_ohep_task is not universe polymorphic
refine_ohep_task is opaque
Expands to: Constant prosa.implementation.refinements.FP.refinements.refine_ohep_task
Declared in library prosa.implementation.refinements.FP.refinements, line 170, characters 16-32
refine_ohep_task
     : @refines (Equality.sort Task -> Equality.sort Task -> bool) (@task_T N -> @task_T N -> bool)
         (Rtask ==> Rtask ==> bool_R) ohep_task (@ohep_task_T N leq_N eq_task)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.refine_ohep_task : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
      Prosa.Implementation.Refinements.Refinements.bool_R))
  Prosa.Implementation.Refinements.FP.FastSearchSpace.ohep_task
  Prosa.Implementation.Refinements.FP.Refinements.ohep_task_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_refine_ohep_task
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Task_Task -> Prosa_Implementation_Refinements_Task_Task -> Bool)
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N -> Bool)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Prosa_Implementation_Refinements_Task_Task
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Refinements_Task_Task -> Bool)
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
             Bool)
            Prosa_Implementation_Refinements_Task_Rtask
            (Prosa_Implementation_Refinements_Refinements_hrespectful
               Prosa_Implementation_Refinements_Task_Task
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Bool Bool Prosa_Implementation_Refinements_Task_Rtask
               Prosa_Implementation_Refinements_Refinements_bool_R))
         Prosa_Implementation_Refinements_FP_FastSearchSpace_ohep_task
         (Prosa_Implementation_Refinements_FP_Refinements_ohep_task_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_leq_N
            Prosa_Implementation_Refinements_FP_Refinements_eq_task)
```
