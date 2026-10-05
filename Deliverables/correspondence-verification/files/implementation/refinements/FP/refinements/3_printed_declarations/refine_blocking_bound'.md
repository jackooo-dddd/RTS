# `refine_blocking_bound'`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.refinements.refine_blocking_bound'`
- Lean: `Prosa.Implementation.Refinements.FP.Refinements.refine_blocking_bound'`
- Certificate: `refine_blocking_bound'_correspondence`

## Official Rocq

```coq
refine_blocking_bound' :
forall (ts : seq (@task_T N)) (tsk : @task_T N),
@refines nat N Rnat (blocking_bound_NP [seq taskT_to_task i | i <- ts] (taskT_to_task tsk))
  (@blocking_bound_NP_T N zero_N one_N sub_N leq_N lt_N ts tsk)

refine_blocking_bound' is not universe polymorphic
Arguments refine_blocking_bound' ts%_seq_scope tsk
refine_blocking_bound' is opaque
Expands to: Constant prosa.implementation.refinements.FP.refinements.refine_blocking_bound'
Declared in library prosa.implementation.refinements.FP.refinements, line 235, characters 16-38
refine_blocking_bound'
     : forall (ts : seq (@task_T N)) (tsk : @task_T N),
       @refines nat N Rnat (blocking_bound_NP [seq taskT_to_task i | i <- ts] (taskT_to_task tsk))
         (@blocking_bound_NP_T N zero_N one_N sub_N leq_N lt_N ts tsk)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.Refinements.refine_blocking_bound' : (ts :
    List (Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N)) →
  (tsk : Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N) →
    Prosa.Implementation.Refinements.Refinements.refines Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.FP.FastSearchSpace.blocking_bound_NP
        (List.map Prosa.Implementation.Refinements.Task.taskT_to_task ts)
        (Prosa.Implementation.Refinements.Task.taskT_to_task tsk))
      (Prosa.Implementation.Refinements.FP.Refinements.blocking_bound_NP_T ts tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_Refinements_refine_blocking_bound'
     : forall
         (ts : List_inst1
                 (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N))
         (tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N),
       Prosa_Implementation_Refinements_Refinements_refines Nat
         Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_Rnat
         (Prosa_Implementation_Refinements_FP_FastSearchSpace_blocking_bound_NP
            (List_map_inst3
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Task Prosa_Implementation_Refinements_Task_taskT_to_task
               ts)
            (Prosa_Implementation_Refinements_Task_taskT_to_task tsk))
         (Prosa_Implementation_Refinements_FP_Refinements_blocking_bound_NP_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_sub_N
            Prosa_Implementation_Refinements_Refinements_leq_N
            Prosa_Implementation_Refinements_Refinements_lt_N ts tsk)
```
