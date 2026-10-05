# `refine_task_eqdef`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.refine_task_eqdef`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.refine_task_eqdef`
- Certificate: `refine_task_eqdef_correspondence`

## Official Rocq

```coq
refine_task_eqdef :
@refines (Equality.sort Task -> Equality.sort Task -> bool) (@task_T N -> @task_T N -> bool)
  (Rtask ==> Rtask ==> bool_R) task_eqdef (@task_eqdef_T N eq_N eq_taskab)

refine_task_eqdef is not universe polymorphic
refine_task_eqdef is opaque
Expands to: Constant prosa.implementation.refinements.FP.refinements.refine_task_eqdef
Declared in library prosa.implementation.refinements.FP.refinements, line 160, characters 16-33
refine_task_eqdef
     : @refines (Equality.sort Task -> Equality.sort Task -> bool) (@task_T N -> @task_T N -> bool)
         (Rtask ==> Rtask ==> bool_R) task_eqdef (@task_eqdef_T N eq_N eq_taskab)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.refine_task_eqdef : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
      Prosa.Implementation.Refinements.Refinements.bool_R))
  Prosa.Implementation.Definitions.Task.task_eqdef Prosa.Implementation.Refinements.Task.task_eqdef_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_refine_task_eqdef
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
         Prosa_Implementation_Definitions_Task_task_eqdef
         (Prosa_Implementation_Refinements_Task_task_eqdef_T Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_eq_N
            Prosa_Implementation_Refinements_FP_Refinements_eq_taskab)
```
