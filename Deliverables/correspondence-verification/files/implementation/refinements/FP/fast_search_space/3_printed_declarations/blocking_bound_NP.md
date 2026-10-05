# `blocking_bound_NP`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.fast_search_space.blocking_bound_NP`
- Lean: `Prosa.Implementation.Refinements.FP.FastSearchSpace.blocking_bound_NP`
- Certificate: `blocking_bound_NP_correspondence`

## Official Rocq

```coq
blocking_bound_NP : seq (Equality.sort Task) -> Equality.sort Task -> nat

blocking_bound_NP is not universe polymorphic
Arguments blocking_bound_NP ts%_seq_scope tsk
blocking_bound_NP is transparent
Expands to: Constant prosa.implementation.refinements.FP.fast_search_space.blocking_bound_NP
Declared in library prosa.implementation.refinements.FP.fast_search_space, line 26, characters 11-28
blocking_bound_NP
     : seq (Equality.sort Task) -> Equality.sort Task -> nat
```

Body:

```coq
blocking_bound_NP =
fun (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) =>
\max_(tsk_other <- ts | ~~ @hep_task Task (@NumericFPAscending Task TaskPriority) tsk_other tsk)
   (@concept.task_cost Task TaskCost tsk_other - 1)
     : seq (Equality.sort Task) -> Equality.sort Task -> nat

Arguments blocking_bound_NP ts%_seq_scope tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.FastSearchSpace.blocking_bound_NP : List
    Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.FastSearchSpace.blocking_bound_NP : List
    Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → ℕ :=
fun ts tsk =>
  Prosa.Util.Sum.maxFiltered ts (fun tsk_other => !Prosa.Model.Priority.Definitions.hep_task tsk_other tsk)
    fun tsk_other => Prosa.Model.Task.Concept.task_cost tsk_other - 1
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_blocking_bound_NP
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Nat
```

Body:

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_blocking_bound_NP@{} =
fun (ts : List_inst1 Prosa_Implementation_Refinements_Task_Task)
  (tsk : Prosa_Implementation_Refinements_Task_Task) =>
Prosa_Util_Sum_maxFiltered_inst1 Prosa_Implementation_Refinements_Task_Task ts
  (fun tsk_other : Prosa_Implementation_Refinements_Task_Task =>
   Bool_not
     (Prosa_Model_Priority_Definitions_FP_policy_hep_task_inst1 Prosa_Implementation_Refinements_Task_Task
        Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
        (Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1
           Prosa_Implementation_Refinements_Task_Task
           Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
           Prosa_Implementation_Definitions_Task_TaskPriority)
        tsk_other tsk))
  (fun tsk_other : Prosa_Implementation_Refinements_Task_Task =>
   HSub_hSub_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
     (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
     (Prosa_Model_Task_Concept_TaskCost_task_cost_inst1 Prosa_Implementation_Refinements_Task_Task
        Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
        Prosa_Implementation_Definitions_Task_TaskCost tsk_other)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Nat

Arguments Prosa_Implementation_Refinements_FP_FastSearchSpace_blocking_bound_NP ts tsk
```
