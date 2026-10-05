# `refine_bound_on_total_hep_workload`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.EDF.refinements.refine_bound_on_total_hep_workload`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.refine_bound_on_total_hep_workload`
- Certificate: `refine_bound_on_total_hep_workload_correspondence`

## Official Rocq

```coq
refine_bound_on_total_hep_workload :
@refines (seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat -> nat)
  (seq (@task_T N) -> @task_T N -> N -> N -> N)
  (@list_R (Equality.sort task.Task) (@task_T N) Rtask ==> Rtask ==> Rnat ==> Rnat ==> Rnat)
  bound_on_total_hep_workload
  (@bound_on_total_hep_workload_T N zero_N one_N sub_N add_N mul_N div_N mod_N leq_N lt_N eq_task)

refine_bound_on_total_hep_workload is not universe polymorphic
refine_bound_on_total_hep_workload is opaque
Expands to: Constant prosa.implementation.refinements.EDF.refinements.refine_bound_on_total_hep_workload
Declared in library prosa.implementation.refinements.EDF.refinements, line 195, characters 16-50
refine_bound_on_total_hep_workload
     : @refines (seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat -> nat)
         (seq (@task_T N) -> @task_T N -> N -> N -> N)
         (@list_R (Equality.sort task.Task) (@task_T N) Rtask ==> Rtask ==> Rnat ==> Rnat ==> Rnat)
         bound_on_total_hep_workload
         (@bound_on_total_hep_workload_T N zero_N one_N sub_N add_N mul_N div_N mod_N leq_N lt_N eq_task)
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.refine_bound_on_total_hep_workload : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Task.Rtask)
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
      (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
        (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
          Prosa.Implementation.Refinements.Refinements.Rnat))))
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.bound_on_total_hep_workload
  Prosa.Implementation.Refinements.EDF.Refinements.bound_on_total_hep_workload_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_refine_bound_on_total_hep_workload
     : Prosa_Implementation_Refinements_Refinements_refines
         (List_inst1 Prosa_Implementation_Refinements_Task_Task ->
          Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat -> Nat)
         (List_inst1
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N) ->
          Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful
            (List_inst1 Prosa_Implementation_Refinements_Task_Task)
            (List_inst1
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N))
            (Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat -> Nat)
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Refinements_Refinements_list_R Prosa_Implementation_Refinements_Task_Task
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Rtask)
            (Prosa_Implementation_Refinements_Refinements_hrespectful
               Prosa_Implementation_Refinements_Task_Task
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               (Nat -> Nat -> Nat)
               (Prosa_Implementation_Refinements_Refinements_N ->
                Prosa_Implementation_Refinements_Refinements_N ->
                Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Rtask
               (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
                  Prosa_Implementation_Refinements_Refinements_N (Nat -> Nat)
                  (Prosa_Implementation_Refinements_Refinements_N ->
                   Prosa_Implementation_Refinements_Refinements_N)
                  Prosa_Implementation_Refinements_Refinements_Rnat
                  (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
                     Prosa_Implementation_Refinements_Refinements_N Nat
                     Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_Rnat
                     Prosa_Implementation_Refinements_Refinements_Rnat))))
         Prosa_Implementation_Refinements_EDF_FastSearchSpace_bound_on_total_hep_workload
         (Prosa_Implementation_Refinements_EDF_Refinements_bound_on_total_hep_workload_T
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
