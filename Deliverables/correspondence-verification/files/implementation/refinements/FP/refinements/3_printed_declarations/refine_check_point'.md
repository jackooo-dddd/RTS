# `refine_check_point'`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.refine_check_point'`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.refine_check_point'`
- Certificate: `refine_check_point'_correspondence`

## Official Rocq

```coq
refine_check_point' :
forall (ts : seq (@task_T N)) (tsk : @task_T N),
@refines (nat -> nat * nat -> bool) (N -> N * N -> bool) (Rnat ==> @prod_R nat N Rnat nat N Rnat ==> bool_R)
  (check_point_FP [seq taskT_to_task i | i <- ts] (taskT_to_task tsk))
  (@check_point_FP_T N zero_N one_N add_N mul_N div_N mod_N leq_N eq_task ts tsk)

refine_check_point' is not universe polymorphic
Arguments refine_check_point' ts%_seq_scope tsk
refine_check_point' is opaque
Expands to: Constant prosa.implementation.refinements.FP.refinements.refine_check_point'
Declared in library prosa.implementation.refinements.FP.refinements, line 206, characters 16-35
refine_check_point'
     : forall (ts : seq (@task_T N)) (tsk : @task_T N),
       @refines (nat -> nat * nat -> bool) (N -> N * N -> bool)
         (Rnat ==> @prod_R nat N Rnat nat N Rnat ==> bool_R)
         (check_point_FP [seq taskT_to_task i | i <- ts] (taskT_to_task tsk))
         (@check_point_FP_T N zero_N one_N add_N mul_N div_N mod_N leq_N eq_task ts tsk)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.refine_check_point' : (ts :
    List (Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N)) →
  (tsk : Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
    Prosa.Implementation.Refinements.Refinements.refines
      (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
        (Prosa.Implementation.Refinements.Refinements.hrespectful
          (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
            Prosa.Implementation.Refinements.Refinements.Rnat)
          Prosa.Implementation.Refinements.Refinements.bool_R))
      (Prosa.Implementation.Refinements.FP.FastSearchSpace.check_point_FP
        (List.map Prosa.Implementation.Refinements.Task.taskT_to_task ts)
        (Prosa.Implementation.Refinements.Task.taskT_to_task tsk))
      (Prosa.Implementation.Refinements.FP.Refinements.check_point_FP_T ts tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_refine_check_point'
     : forall
         (ts : List_inst1
                 (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N))
         (tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N),
       Prosa_Implementation_Refinements_Refinements_refines (Nat -> Prod_inst3 Nat Nat -> Bool)
         (Prosa_Implementation_Refinements_Refinements_N ->
          Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N ->
          Bool)
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
               Prosa_Implementation_Refinements_Refinements_bool_R))
         (Prosa_Implementation_Refinements_FP_FastSearchSpace_check_point_FP
            (List_map_inst3
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Task Prosa_Implementation_Refinements_Task_taskT_to_task
               ts)
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsk))
         (Prosa_Implementation_Refinements_FP_Refinements_check_point_FP_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_mul_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_leq_N
            Prosa_Implementation_Refinements_FP_Refinements_eq_task ts tsk)
```
