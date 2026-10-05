# `refine_check_point_FP`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.EDF.refinements.refine_check_point_FP`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.refine_check_point_FP`
- Certificate: `refine_check_point_FP_correspondence`

## Official Rocq

```coq
refine_check_point_FP :
@refines (seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat * nat -> bool)
  (seq (@task_T N) -> @task_T N -> N -> N * N -> bool)
  (@list_R (Equality.sort task.Task) (@task_T N) Rtask ==>
   Rtask ==> Rnat ==> @prod_R nat N Rnat nat N Rnat ==> bool_R)
  check_point_FP (@check_point_FP_T N zero_N one_N sub_N add_N mul_N div_N mod_N leq_N lt_N eq_task)

refine_check_point_FP is not universe polymorphic
refine_check_point_FP is opaque
Expands to: Constant prosa.implementation.refinements.EDF.refinements.refine_check_point_FP
Declared in library prosa.implementation.refinements.EDF.refinements, line 207, characters 16-37
refine_check_point_FP
     : @refines (seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat * nat -> bool)
         (seq (@task_T N) -> @task_T N -> N -> N * N -> bool)
         (@list_R (Equality.sort task.Task) (@task_T N) Rtask ==>
          Rtask ==> Rnat ==> @prod_R nat N Rnat nat N Rnat ==> bool_R)
         check_point_FP (@check_point_FP_T N zero_N one_N sub_N add_N mul_N div_N mod_N leq_N lt_N eq_task)
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.refine_check_point_FP : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Task.Rtask)
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
      (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
        (Prosa.Implementation.Refinements.Refinements.hrespectful
          (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
            Prosa.Implementation.Refinements.Refinements.Rnat)
          Prosa.Implementation.Refinements.Refinements.bool_R))))
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.check_point_FP
  Prosa.Implementation.Refinements.EDF.Refinements.check_point_FP_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_refine_check_point_FP
     : Prosa_Implementation_Refinements_Refinements_refines
         (List_inst1 Prosa_Implementation_Refinements_Task_Task ->
          Prosa_Implementation_Refinements_Task_Task -> Nat -> Prod_inst3 Nat Nat -> Bool)
         (List_inst1
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) ->
          Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N ->
          Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N ->
          Bool)
         (Prosa_Implementation_Refinements_Refinements_hrespectful
            (List_inst1 Prosa_Implementation_Refinements_Task_Task)
            (List_inst1
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N))
            (Prosa_Implementation_Refinements_Task_Task -> Nat -> Prod_inst3 Nat Nat -> Bool)
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Refinements_N ->
             Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N ->
             Bool)
            (Prosa_Implementation_Refinements_Refinements_list_R Prosa_Implementation_Refinements_Task_Task
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Rtask)
            (Prosa_Implementation_Refinements_Refinements_hrespectful
               Prosa_Implementation_Refinements_Task_Task
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               (Nat -> Prod_inst3 Nat Nat -> Bool)
               (Prosa_Implementation_Refinements_Refinements_N ->
                Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N ->
                Bool)
               Prosa_Implementation_Refinements_Task_Rtask
               (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
                  Prosa_Implementation_Refinements_Refinements_N (Prod_inst3 Nat Nat -> Bool)
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N ->
                   Bool)
                  Prosa_Implementation_Refinements_Refinements_Rnat
                  (Prosa_Implementation_Refinements_Refinements_hrespectful (Prod_inst3 Nat Nat)
                     (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                        Prosa_Implementation_Refinements_Refinements_N)
                     Bool Bool
                     (Prosa_Implementation_Refinements_Refinements_prod_R Nat
                        Prosa_Implementation_Refinements_Refinements_N
                        Prosa_Implementation_Refinements_Refinements_Rnat Nat
                        Prosa_Implementation_Refinements_Refinements_N
                        Prosa_Implementation_Refinements_Refinements_Rnat)
                     Prosa_Implementation_Refinements_Refinements_bool_R))))
         Prosa_Implementation_Refinements_EDF_FastSearchSpace_check_point_FP
         (Prosa_Implementation_Refinements_EDF_Refinements_check_point_FP_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_sub_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_mul_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_leq_N
            Prosa_Implementation_Refinements_Refinements_lt_N
            Prosa_Implementation_Refinements_EDF_Refinements_eq_task)
```
