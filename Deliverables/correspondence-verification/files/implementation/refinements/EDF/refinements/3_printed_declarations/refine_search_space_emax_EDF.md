# `refine_search_space_emax_EDF`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.EDF.refinements.refine_search_space_emax_EDF`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.refine_search_space_emax_EDF`
- Certificate: `refine_search_space_emax_EDF_correspondence`

## Official Rocq

```coq
refine_search_space_emax_EDF :
forall (ts : seq (@task_T N)) (tsk : @task_T N),
@refines (nat -> seq nat) (N -> seq N) (Rnat ==> @list_R nat N Rnat)
  (search_space_emax_EDF [seq taskT_to_task i | i <- ts] (taskT_to_task tsk))
  (search_space_emax_EDF_N ts tsk)

refine_search_space_emax_EDF is not universe polymorphic
Arguments refine_search_space_emax_EDF ts%_seq_scope tsk
refine_search_space_emax_EDF is opaque
Expands to: Constant prosa.implementation.refinements.EDF.refinements.refine_search_space_emax_EDF
Declared in library prosa.implementation.refinements.EDF.refinements, line 118, characters 16-44
refine_search_space_emax_EDF
     : forall (ts : seq (@task_T N)) (tsk : @task_T N),
       @refines (nat -> seq nat) (N -> seq N) (Rnat ==> @list_R nat N Rnat)
         (search_space_emax_EDF [seq taskT_to_task i | i <- ts] (taskT_to_task tsk))
         (search_space_emax_EDF_N ts tsk)
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.refine_search_space_emax_EDF : (ts :
    List (Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N)) →
  (tsk : Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
    Prosa.Implementation.Refinements.Refinements.refines
      (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
        (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat))
      (Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_EDF
        (List.map Prosa.Implementation.Refinements.Task.taskT_to_task ts)
        (Prosa.Implementation.Refinements.Task.taskT_to_task tsk))
      (Prosa.Implementation.Refinements.EDF.Refinements.search_space_emax_EDF_N ts tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_refine_search_space_emax_EDF
     : forall
         (ts : List_inst1
                 (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N))
         (tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N),
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
         (Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_EDF
            (List_map_inst3
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
               Prosa_Implementation_Refinements_Task_taskT_to_task ts)
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsk))
         (Prosa_Implementation_Refinements_EDF_Refinements_search_space_emax_EDF_N ts tsk)
```
