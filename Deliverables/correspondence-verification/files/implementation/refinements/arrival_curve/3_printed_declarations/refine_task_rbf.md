# `refine_task_rbf`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.arrival_curve.refine_task_rbf`
- Lean: `Prosa.Implementation.Refinements.ArrivalCurve.refine_task_rbf`
- Certificate: `refine_task_rbf_correspondence`

## Official Rocq

```coq
refine_task_rbf :
@refines (Equality.sort Task -> nat -> nat) (@task_T binnat.N -> binnat.N -> binnat.N)
  (Rtask ==> Rnat ==> Rnat) task_rbf (@task_rbf_T binnat.N zero_N one_N add_N mul_N div_N mod_N leq_N)

refine_task_rbf is not universe polymorphic
refine_task_rbf is opaque
Expands to: Constant prosa.implementation.refinements.arrival_curve.refine_task_rbf
Declared in library prosa.implementation.refinements.arrival_curve, line 368, characters 18-33
refine_task_rbf
     : @refines (Equality.sort Task -> nat -> nat) (@task_T binnat.N -> binnat.N -> binnat.N)
         (Rtask ==> Rnat ==> Rnat) task_rbf (@task_rbf_T binnat.N zero_N one_N add_N mul_N div_N mod_N leq_N)
```

## Lean

```lean
Prosa.Implementation.Refinements.ArrivalCurve.refine_task_rbf : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Task.Rtask
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.Rnat))
  Prosa.Implementation.Refinements.ArrivalCurve.task_rbf Prosa.Implementation.Refinements.Task.task_rbf_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_ArrivalCurve_refine_task_rbf
     : Prosa_Implementation_Refinements_Refinements_refines
         (Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat)
         (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Prosa_Implementation_Refinements_Task_Task
            (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
            (Nat -> Nat)
            (Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Refinements_Task_Rtask
            (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
               Prosa_Implementation_Refinements_Refinements_N Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat
               Prosa_Implementation_Refinements_Refinements_Rnat))
         Prosa_Implementation_Refinements_ArrivalCurve_task_rbf
         (Prosa_Implementation_Refinements_Task_task_rbf_T Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_mul_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_leq_N)
```
