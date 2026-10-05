# `refine_search_space_emax`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.refine_search_space_emax`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.refine_search_space_emax`
- Certificate: `refine_search_space_emax_correspondence`

## Official Rocq

```coq
refine_search_space_emax :
forall tsk : @task_T N,
@refines (nat -> seq nat) (N -> seq N) (Rnat ==> @list_R nat N Rnat)
  (search_space_emax_FP (taskT_to_task tsk)) (search_space_emax_FP_N tsk)

refine_search_space_emax is not universe polymorphic
Arguments refine_search_space_emax tsk
refine_search_space_emax is opaque
Expands to: Constant prosa.implementation.refinements.FP.refinements.refine_search_space_emax
Declared in library prosa.implementation.refinements.FP.refinements, line 92, characters 16-40
refine_search_space_emax
     : forall tsk : @task_T N,
       @refines (nat -> seq nat) (N -> seq N) (Rnat ==> @list_R nat N Rnat)
         (search_space_emax_FP (taskT_to_task tsk)) (search_space_emax_FP_N tsk)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.refine_search_space_emax : (tsk :
    Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Refinements.Refinements.refines
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat))
    (Prosa.Implementation.Refinements.FP.FastSearchSpace.search_space_emax_FP
      (Prosa.Implementation.Refinements.Task.taskT_to_task tsk))
    (Prosa.Implementation.Refinements.FP.Refinements.search_space_emax_FP_N tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_refine_search_space_emax
     : forall
         tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N,
       Prosa_Implementation_Refinements_Refinements_refines (Nat -> List_inst1 Nat)
         (Prosa_Implementation_Refinements_Refinements_N ->
          List_inst1 Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N (List_inst1 Nat)
            (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Refinements_Refinements_Rnat
            (Prosa_Implementation_Refinements_Refinements_list_R Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat))
         (Prosa_Implementation_Refinements_FP_FastSearchSpace_search_space_emax_FP
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsk))
         (Prosa_Implementation_Refinements_FP_Refinements_search_space_emax_FP_N tsk)
```
