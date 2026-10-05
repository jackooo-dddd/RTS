# `total_hep_rbf`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.fast_search_space.total_hep_rbf`
- Lean: `Prosa.Implementation.Refinements.FP.FastSearchSpace.total_hep_rbf`
- Certificate: `total_hep_rbf_correspondence`

## Official Rocq

```coq
total_hep_rbf : seq (Equality.sort Task) -> Equality.sort Task -> duration -> nat

total_hep_rbf is not universe polymorphic
Arguments total_hep_rbf ts%_seq_scope tsk Δ
total_hep_rbf is transparent
Expands to: Constant prosa.implementation.refinements.FP.fast_search_space.total_hep_rbf
Declared in library prosa.implementation.refinements.FP.fast_search_space, line 13, characters 11-24
total_hep_rbf
     : seq (Equality.sort Task) -> Equality.sort Task -> duration -> nat
```

Body:

```coq
total_hep_rbf =
fun (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) =>
       (@NumericFPAscending Task TaskPriority) tsk]
     : seq (Equality.sort Task) -> Equality.sort Task -> duration -> nat

Arguments total_hep_rbf ts%_seq_scope tsk Δ
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.FastSearchSpace.total_hep_rbf : List Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.FastSearchSpace.total_hep_rbf : List
    Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → Prosa.Behavior.Time.duration → ℕ :=
fun ts tsk Δ => Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP ts tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_total_hep_rbf
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_total_hep_rbf@{} =
fun (ts : List_inst1 Prosa_Implementation_Refinements_Task_Task)
  (tsk : Prosa_Implementation_Refinements_Task_Task) (_UU0394_ : Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP_inst1
  Prosa_Implementation_Refinements_Task_Task
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
  Prosa_Implementation_Definitions_Task_TaskCost Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals ts
  (Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1
     Prosa_Implementation_Refinements_Task_Task
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
     Prosa_Implementation_Definitions_Task_TaskPriority)
  tsk _UU0394_
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Implementation_Refinements_FP_FastSearchSpace_total_hep_rbf ts tsk t
```
