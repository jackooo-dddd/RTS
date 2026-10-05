# `refine_total_ohep_rbf`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.refine_total_ohep_rbf`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.refine_total_ohep_rbf`
- Certificate: `refine_total_ohep_rbf_correspondence`

## Official Rocq

```coq
refine_total_ohep_rbf :
@refines (seq (Equality.sort Task) -> Equality.sort Task -> nat -> nat)
  (seq (@task_T N) -> @task_T N -> N -> N)
  (@list_R (Equality.sort Task) (@task_T N) Rtask ==> Rtask ==> Rnat ==> Rnat) total_ohep_rbf
  (@total_ohep_rbf_T N zero_N one_N add_N mul_N div_N mod_N leq_N eq_task)

refine_total_ohep_rbf is not universe polymorphic
refine_total_ohep_rbf is opaque
Expands to: Constant prosa.implementation.refinements.FP.refinements.refine_total_ohep_rbf
Declared in library prosa.implementation.refinements.FP.refinements, line 181, characters 16-37
refine_total_ohep_rbf
     : @refines (seq (Equality.sort Task) -> Equality.sort Task -> nat -> nat)
         (seq (@task_T N) -> @task_T N -> N -> N)
         (@list_R (Equality.sort Task) (@task_T N) Rtask ==> Rtask ==> Rnat ==> Rnat) total_ohep_rbf
         (@total_ohep_rbf_T N zero_N one_N add_N mul_N div_N mod_N leq_N eq_task)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.refine_total_ohep_rbf : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Task.Rtask)
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
      (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
        Prosa.Implementation.Refinements.Refinements.Rnat)))
  Prosa.Implementation.Refinements.FP.FastSearchSpace.total_ohep_rbf
  Prosa.Implementation.Refinements.FP.Refinements.total_ohep_rbf_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_refine_total_ohep_rbf
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
         Prosa_Implementation_Refinements_FP_FastSearchSpace_total_ohep_rbf
         (Prosa_Implementation_Refinements_FP_Refinements_total_ohep_rbf_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_mul_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_leq_N
            Prosa_Implementation_Refinements_FP_Refinements_eq_task)
```
