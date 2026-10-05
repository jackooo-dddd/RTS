# `refine_blocking_bound`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.refine_blocking_bound`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.refine_blocking_bound`
- Certificate: `refine_blocking_bound_correspondence`

## Official Rocq

```coq
refine_blocking_bound :
@refines (seq (Equality.sort Task) -> Equality.sort Task -> nat) (seq (@task_T N) -> @task_T N -> N)
  (@list_R (Equality.sort Task) (@task_T N) Rtask ==> Rtask ==> Rnat) blocking_bound_NP
  (@blocking_bound_NP_T N zero_N one_N sub_N leq_N lt_N)

refine_blocking_bound is not universe polymorphic
refine_blocking_bound is opaque
Expands to: Constant prosa.implementation.refinements.FP.refinements.refine_blocking_bound
Declared in library prosa.implementation.refinements.FP.refinements, line 221, characters 16-37
refine_blocking_bound
     : @refines (seq (Equality.sort Task) -> Equality.sort Task -> nat) (seq (@task_T N) -> @task_T N -> N)
         (@list_R (Equality.sort Task) (@task_T N) Rtask ==> Rtask ==> Rnat) blocking_bound_NP
         (@blocking_bound_NP_T N zero_N one_N sub_N leq_N lt_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.refine_blocking_bound : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Task.Rtask)
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
      Prosa.Implementation.Refinements.Refinements.Rnat))
  Prosa.Implementation.Refinements.FP.FastSearchSpace.blocking_bound_NP
  Prosa.Implementation.Refinements.FP.Refinements.blocking_bound_NP_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_refine_blocking_bound
     : Prosa_Implementation_Refinements_Refinements_refines
         (List_inst1 Prosa_Implementation_Refinements_Task_Task ->
          Prosa_Implementation_Refinements_Task_Task -> Nat)
         (List_inst1
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) ->
          Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful
            (List_inst1 Prosa_Implementation_Refinements_Task_Task)
            (List_inst1
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N))
            (Prosa_Implementation_Refinements_Task_Task -> Nat)
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Refinements_Refinements_list_R Prosa_Implementation_Refinements_Task_Task
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Rtask)
            (Prosa_Implementation_Refinements_Refinements_hrespectful
               Prosa_Implementation_Refinements_Task_Task
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Nat Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Task_Rtask
               Prosa_Implementation_Refinements_Refinements_Rnat))
         Prosa_Implementation_Refinements_FP_FastSearchSpace_blocking_bound_NP
         (Prosa_Implementation_Refinements_FP_Refinements_blocking_bound_NP_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_sub_N
            Prosa_Implementation_Refinements_Refinements_leq_N
            Prosa_Implementation_Refinements_Refinements_lt_N)
```
