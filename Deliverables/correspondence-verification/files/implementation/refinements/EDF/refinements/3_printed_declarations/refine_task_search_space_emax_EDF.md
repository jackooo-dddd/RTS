# `refine_task_search_space_emax_EDF`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.EDF.refinements.refine_task_search_space_emax_EDF`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.refine_task_search_space_emax_EDF`
- Certificate: `refine_task_search_space_emax_EDF_correspondence`

## Official Rocq

```coq
refine_task_search_space_emax_EDF :
forall tsk tsko : @task_T N,
@refines (nat -> seq nat) (N -> seq N) (Rnat ==> @list_R nat N Rnat)
  (task_search_space_emax_EDF (taskT_to_task tsk) (taskT_to_task tsko))
  (task_search_space_emax_EDF_N tsk tsko)

refine_task_search_space_emax_EDF is not universe polymorphic
Arguments refine_task_search_space_emax_EDF tsk tsko
refine_task_search_space_emax_EDF is opaque
Expands to: Constant prosa.implementation.refinements.EDF.refinements.refine_task_search_space_emax_EDF
Declared in library prosa.implementation.refinements.EDF.refinements, line 103, characters 16-49
refine_task_search_space_emax_EDF
     : forall tsk tsko : @task_T N,
       @refines (nat -> seq nat) (N -> seq N) (Rnat ==> @list_R nat N Rnat)
         (task_search_space_emax_EDF (taskT_to_task tsk) (taskT_to_task tsko))
         (task_search_space_emax_EDF_N tsk tsko)
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.refine_task_search_space_emax_EDF : (tsk tsko :
    Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
  Prosa.Implementation.Refinements.Refinements.refines
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat))
    (Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF
      (Prosa.Implementation.Refinements.Task.taskT_to_task tsk)
      (Prosa.Implementation.Refinements.Task.taskT_to_task tsko))
    (Prosa.Implementation.Refinements.EDF.Refinements.task_search_space_emax_EDF_N tsk tsko)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_refine_task_search_space_emax_EDF
     : forall
         tsk
          tsko : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N,
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
         (Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsk)
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsko))
         (Prosa_Implementation_Refinements_EDF_Refinements_task_search_space_emax_EDF_N tsk tsko)
```
