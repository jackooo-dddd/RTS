# `refine_blocking_bound`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.EDF.refinements.refine_blocking_bound`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.refine_blocking_bound`
- Certificate: `refine_blocking_bound_correspondence`

## Official Rocq

```coq
refine_blocking_bound :
@refines (seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat)
  (seq (@task_T N) -> @task_T N -> N -> N)
  (@list_R (Equality.sort task.Task) (@task_T N) Rtask ==> Rtask ==> Rnat ==> Rnat) blocking_bound_NP
  (@blocking_bound_NP_T N zero_N one_N sub_N add_N mul_N div_N mod_N leq_N lt_N)

refine_blocking_bound is not universe polymorphic
refine_blocking_bound is opaque
Expands to: Constant prosa.implementation.refinements.EDF.refinements.refine_blocking_bound
Declared in library prosa.implementation.refinements.EDF.refinements, line 234, characters 16-37
refine_blocking_bound
     : @refines (seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat)
         (seq (@task_T N) -> @task_T N -> N -> N)
         (@list_R (Equality.sort task.Task) (@task_T N) Rtask ==> Rtask ==> Rnat ==> Rnat) blocking_bound_NP
         (@blocking_bound_NP_T N zero_N one_N sub_N add_N mul_N div_N mod_N leq_N lt_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.refine_blocking_bound : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Task.Rtask)
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
      (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
        Prosa.Implementation.Refinements.Refinements.Rnat)))
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.blocking_bound_NP
  Prosa.Implementation.Refinements.EDF.Refinements.blocking_bound_NP_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_refine_blocking_bound
     : Prosa_Implementation_Refinements_Refinements_refines
         (List_inst1 Prosa_Implementation_Refinements_Task_Task ->
          Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat)
         (List_inst1
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) ->
          Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful
            (List_inst1 Prosa_Implementation_Refinements_Task_Task)
            (List_inst1
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N))
            (Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat)
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Refinements_Refinements_list_R Prosa_Implementation_Refinements_Task_Task
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Rtask)
            (Prosa_Implementation_Refinements_Refinements_hrespectful
               Prosa_Implementation_Refinements_Task_Task
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               (Nat -> Nat)
               (Prosa_Implementation_Refinements_Refinements_N ->
                Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Rtask
               (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
                  Prosa_Implementation_Refinements_Refinements_N Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat
                  Prosa_Implementation_Refinements_Refinements_Rnat)))
         Prosa_Implementation_Refinements_EDF_FastSearchSpace_blocking_bound_NP
         (Prosa_Implementation_Refinements_EDF_Refinements_blocking_bound_NP_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_sub_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_mul_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_leq_N
            Prosa_Implementation_Refinements_Refinements_lt_N)
```
