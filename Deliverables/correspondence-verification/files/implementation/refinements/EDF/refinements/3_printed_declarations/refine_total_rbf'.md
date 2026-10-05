# `refine_total_rbf'`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.EDF.refinements.refine_total_rbf'`
- Lean: `Prosa.Implementation.Refinements.EDF.Refinements.refine_total_rbf'`
- Certificate: `refine_total_rbf'_correspondence`

## Official Rocq

```coq
refine_total_rbf' :
forall ts : seq (@task_T N),
@refines (nat -> nat) (N -> N) (Rnat ==> Rnat)
  (@total_request_bound_function task.Task TaskCost ConcreteMaxArrivals [seq taskT_to_task i | i <- ts])
  (@total_rbf_T N zero_N one_N add_N mul_N div_N mod_N leq_N ts)

refine_total_rbf' is not universe polymorphic
Arguments refine_total_rbf' ts%_seq_scope
refine_total_rbf' is opaque
Expands to: Constant prosa.implementation.refinements.EDF.refinements.refine_total_rbf'
Declared in library prosa.implementation.refinements.EDF.refinements, line 159, characters 16-33
refine_total_rbf'
     : forall ts : seq (@task_T N),
       @refines (nat -> nat) (N -> N) (Rnat ==> Rnat)
         (@total_request_bound_function task.Task TaskCost ConcreteMaxArrivals
            [seq taskT_to_task i | i <- ts])
         (@total_rbf_T N zero_N one_N add_N mul_N div_N mod_N leq_N ts)
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.Refinements.refine_total_rbf' : (ts :
    List (Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N)) →
  Prosa.Implementation.Refinements.Refinements.refines
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      Prosa.Implementation.Refinements.Refinements.Rnat)
    (Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function
      (List.map Prosa.Implementation.Refinements.Task.taskT_to_task ts))
    (Prosa.Implementation.Refinements.EDF.Refinements.total_rbf_T ts)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_Refinements_refine_total_rbf'
     : forall
         ts : List_inst1
                (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N),
       Prosa_Implementation_Refinements_Refinements_refines (Nat -> Nat)
         (Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N Nat Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_Rnat
            Prosa_Implementation_Refinements_Refinements_Rnat)
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function_inst1
            Prosa_Implementation_Refinements_Task_Task
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
            Prosa_Implementation_Definitions_Task_TaskCost
            Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals
            (List_map_inst3
               (Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Task_Task Prosa_Implementation_Refinements_Task_taskT_to_task
               ts))
         (Prosa_Implementation_Refinements_EDF_Refinements_total_rbf_T
            Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N
            Prosa_Implementation_Refinements_Refinements_mul_N
            Prosa_Implementation_Refinements_Refinements_div_N
            Prosa_Implementation_Refinements_Refinements_mod_N
            Prosa_Implementation_Refinements_Refinements_leq_N ts)
```
