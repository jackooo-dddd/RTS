# `total_ohep_rbf`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.fast_search_space.total_ohep_rbf`
- Lean: `Prosa.Implementation.Refinements.FP.FastSearchSpace.total_ohep_rbf`
- Certificate: `total_ohep_rbf_correspondence`

## Official Rocq

```coq
total_ohep_rbf : seq (Equality.sort Task) -> Equality.sort Task -> duration -> nat

total_ohep_rbf is not universe polymorphic
Arguments total_ohep_rbf ts%_seq_scope tsk Δ
total_ohep_rbf is transparent
Expands to: Constant prosa.implementation.refinements.FP.fast_search_space.total_ohep_rbf
Declared in library prosa.implementation.refinements.FP.fast_search_space, line 17, characters 11-25
total_ohep_rbf
     : seq (Equality.sort Task) -> Equality.sort Task -> duration -> nat
```

Body:

```coq
total_ohep_rbf =
fun (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) =>
       (@NumericFPAscending Task TaskPriority) tsk]
     : seq (Equality.sort Task) -> Equality.sort Task -> duration -> nat

Arguments total_ohep_rbf ts%_seq_scope tsk Δ
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.FastSearchSpace.total_ohep_rbf : List Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.FastSearchSpace.total_ohep_rbf : List
    Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → Prosa.Behavior.Time.duration → ℕ :=
fun ts tsk Δ => Prosa.Analysis.Definitions.RequestBoundFunction.total_ohep_request_bound_function_FP ts tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_total_ohep_rbf
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_total_ohep_rbf@{} =
fun (ts : List_inst1 Prosa_Implementation_Refinements_Task_Task)
  (tsk : Prosa_Implementation_Refinements_Task_Task) (_UU0394_ : Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP_inst1
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

Arguments Prosa_Implementation_Refinements_FP_FastSearchSpace_total_ohep_rbf ts tsk t
```
