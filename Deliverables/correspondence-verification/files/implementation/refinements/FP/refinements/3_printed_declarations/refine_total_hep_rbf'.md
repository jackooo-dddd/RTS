# `refine_total_hep_rbf'`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.refine_total_hep_rbf'`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.refine_total_hep_rbf'`
- Certificate: `refine_total_hep_rbf'_correspondence`

## Official Rocq

```coq
refine_total_hep_rbf' :
forall (ts : seq (@task_T N)) (tsk : @task_T N),
@refines (nat -> nat) (N -> N) (Rnat ==> Rnat)
  (total_hep_rbf [seq taskT_to_task i | i <- ts] (taskT_to_task tsk))
  (@total_hep_rbf_T N zero_N one_N add_N mul_N div_N mod_N leq_N ts tsk)

refine_total_hep_rbf' is not universe polymorphic
Arguments refine_total_hep_rbf' ts%_seq_scope tsk
refine_total_hep_rbf' is opaque
Expands to: Constant prosa.implementation.refinements.FP.refinements.refine_total_hep_rbf'
Declared in library prosa.implementation.refinements.FP.refinements, line 133, characters 16-37
refine_total_hep_rbf'
     : forall (ts : seq (@task_T N)) (tsk : @task_T N),
       @refines (nat -> nat) (N -> N) (Rnat ==> Rnat)
         (total_hep_rbf [seq taskT_to_task i | i <- ts] (taskT_to_task tsk))
         (@total_hep_rbf_T N zero_N one_N add_N mul_N div_N mod_N leq_N ts tsk)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.refine_total_hep_rbf' : (ts :
    List (Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N)) →
  (tsk : Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
    Prosa.Implementation.Refinements.Refinements.refines
      (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
        Prosa.Implementation.Refinements.Refinements.Rnat)
      (Prosa.Implementation.Refinements.FP.FastSearchSpace.total_hep_rbf
        (List.map Prosa.Implementation.Refinements.Task.taskT_to_task ts)
        (Prosa.Implementation.Refinements.Task.taskT_to_task tsk))
      (Prosa.Implementation.Refinements.FP.Refinements.total_hep_rbf_T ts tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_refine_total_hep_rbf'
     : forall
         (ts : List_inst1
                 (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N))
         (tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N),
       Prosa_Implementation_Refinements_Refinements_refines (Nat -> Nat)
         (Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N Nat Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_Rnat
            Prosa_Implementation_Refinements_Refinements_Rnat)
         (Prosa_Implementation_Refinements_FP_FastSearchSpace_total_hep_rbf
            (List_map_inst3
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Task Prosa_Implementation_Refinements_Task_taskT_to_task
               ts)
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsk))
         (Prosa_Implementation_Refinements_FP_Refinements_total_hep_rbf_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_mul_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_leq_N ts tsk)
```
