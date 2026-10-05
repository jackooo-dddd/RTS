# `ohep_task`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.fast_search_space.ohep_task`
- Lean: `Prosa.Implementation.Refinements.FP.FastSearchSpace.ohep_task`
- Certificate: `ohep_task_correspondence`

## Official Rocq

```coq
ohep_task : Equality.sort Task -> Equality.sort Task -> bool

ohep_task is not universe polymorphic
Arguments ohep_task tsk1 tsk2
ohep_task is transparent
Expands to: Constant prosa.implementation.refinements.FP.fast_search_space.ohep_task
Declared in library prosa.implementation.refinements.FP.fast_search_space, line 8, characters 11-20
ohep_task
     : Equality.sort Task -> Equality.sort Task -> bool
```

Body:

```coq
ohep_task =
fun tsk1 tsk2 : Equality.sort Task =>
@hep_task Task (@NumericFPAscending Task TaskPriority) tsk1 tsk2 && (tsk1 != tsk2)
     : Equality.sort Task -> Equality.sort Task -> bool

Arguments ohep_task tsk1 tsk2
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.FastSearchSpace.ohep_task : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → Bool
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.FastSearchSpace.ohep_task : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → Bool :=
fun tsk1 tsk2 => Prosa.Model.Priority.Definitions.hep_task tsk1 tsk2 && decide (tsk1 ≠ tsk2)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_ohep_task
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Implementation_Refinements_Task_Task -> Bool
```

Body:

```coq
Prosa_Implementation_Refinements_FP_FastSearchSpace_ohep_task@{} =
fun tsk1 tsk2 : Prosa_Implementation_Refinements_Task_Task =>
Bool_and
  (Prosa_Model_Priority_Definitions_FP_policy_hep_task_inst1 Prosa_Implementation_Refinements_Task_Task
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
     (Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1
        Prosa_Implementation_Refinements_Task_Task
        Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
        Prosa_Implementation_Definitions_Task_TaskPriority)
     tsk1 tsk2)
  (Decidable_decide (Ne Prosa_Implementation_Refinements_Task_Task tsk1 tsk2)
     (instDecidableNot (@eq Prosa_Implementation_Refinements_Task_Task tsk1 tsk2)
        (Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task tsk1 tsk2)))
     : Prosa_Implementation_Refinements_Task_Task -> Prosa_Implementation_Refinements_Task_Task -> Bool

Arguments Prosa_Implementation_Refinements_FP_FastSearchSpace_ohep_task tsk1 tsk
```
