# `refine_hep_task`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.refine_hep_task`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.refine_hep_task`
- Certificate: `refine_hep_task_correspondence`

## Official Rocq

```coq
refine_hep_task :
@refines (Equality.sort Task -> Equality.sort Task -> bool) (@task_T N -> @task_T N -> bool)
  (Rtask ==> Rtask ==> bool_R) (@hep_task Task (@NumericFPAscending Task TaskPriority)) 
  (@hep_task_T N leq_N)

refine_hep_task is not universe polymorphic
refine_hep_task is opaque
Expands to: Constant prosa.implementation.refinements.FP.refinements.refine_hep_task
Declared in library prosa.implementation.refinements.FP.refinements, line 106, characters 16-31
refine_hep_task
     : @refines (Equality.sort Task -> Equality.sort Task -> bool) (@task_T N -> @task_T N -> bool)
         (Rtask ==> Rtask ==> bool_R) (@hep_task Task (@NumericFPAscending Task TaskPriority))
         (@hep_task_T N leq_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.refine_hep_task : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
      Prosa.Implementation.Refinements.Refinements.bool_R))
  Prosa.Model.Priority.Definitions.hep_task Prosa.Implementation.Refinements.FP.Refinements.hep_task_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_refine_hep_task
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
         (Prosa_Model_Priority_Definitions_FP_policy_hep_task_inst1
            Prosa_Implementation_Refinements_Task_Task
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
            (Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1
               Prosa_Implementation_Refinements_Task_Task
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
               Prosa_Implementation_Definitions_Task_TaskPriority))
         (Prosa_Implementation_Refinements_FP_Refinements_hep_task_T
            Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_leq_N)
```
