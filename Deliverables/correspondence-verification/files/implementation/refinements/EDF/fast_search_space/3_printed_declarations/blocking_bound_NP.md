# `blocking_bound_NP`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.fast_search_space.blocking_bound_NP`
- Lean: `Prosa.Implementation.Refinements.EDF.FastSearchSpace.blocking_bound_NP`
- Certificate: `blocking_bound_NP_correspondence`

## Official Rocq

```coq
blocking_bound_NP : seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat

blocking_bound_NP is not universe polymorphic
Arguments blocking_bound_NP ts%_seq_scope tsk A%_nat_scope
blocking_bound_NP is transparent
Expands to: Constant prosa.implementation.refinements.EDF.fast_search_space.blocking_bound_NP
Declared in library prosa.implementation.refinements.EDF.fast_search_space, line 17, characters 11-28
blocking_bound_NP
     : seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat
```

Body:

```coq
blocking_bound_NP =
fun (ts : seq (Equality.sort task.Task)) (tsk : Equality.sort task.Task) (A : nat) =>
\max_(tsk_o <- [seq i | i <- ts] | @blocking_relevant task.Task TaskCost ConcreteMaxArrivals tsk_o &&
                                   (task_deadline tsk + A < task_deadline tsk_o))
   (task_cost tsk_o - 1)
     : seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat

Arguments blocking_bound_NP ts%_seq_scope tsk A%_nat_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.FastSearchSpace.blocking_bound_NP : List
    Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → ℕ → ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.FastSearchSpace.blocking_bound_NP : List
    Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → ℕ → ℕ :=
fun ts tsk A =>
  Prosa.Util.Sum.maxFiltered (List.map (fun i => i) ts)
    (fun tsk_o =>
      Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_relevant tsk_o &&
        decide (Prosa.Model.Task.Concept.task_deadline tsk + A < Prosa.Model.Task.Concept.task_deadline tsk_o))
    fun tsk_o => Prosa.Model.Task.Concept.task_cost tsk_o - 1
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_blocking_bound_NP
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_blocking_bound_NP@{} =
fun (ts : List_inst1 Prosa_Implementation_Refinements_Task_Task)
  (tsk : Prosa_Implementation_Refinements_Task_Task) (A : Nat) =>
Prosa_Util_Sum_maxFiltered_inst1 Prosa_Implementation_Refinements_Task_Task
  (List_map_inst3 Prosa_Implementation_Refinements_Task_Task Prosa_Implementation_Refinements_Task_Task
     (fun i : Prosa_Implementation_Refinements_Task_Task => i) ts)
  (fun tsk_o : Prosa_Implementation_Refinements_Task_Task =>
   Bool_and
     (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_relevant_inst1
        Prosa_Implementation_Refinements_Task_Task
        Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
        Prosa_Implementation_Definitions_Task_TaskCost
        Prosa_Implementation_Definitions_Task_ConcreteMaxArrivals tsk_o)
     (Decidable_decide
        (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
              (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
              (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
                 Prosa_Implementation_Refinements_Task_Task
                 Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                 Prosa_Implementation_Definitions_Task_TaskDeadline tsk)
              A)
           (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
              Prosa_Implementation_Refinements_Task_Task
              Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
              Prosa_Implementation_Definitions_Task_TaskDeadline tsk_o))
        (Nat_decLt
           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
              (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
              (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
                 Prosa_Implementation_Refinements_Task_Task
                 Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                 Prosa_Implementation_Definitions_Task_TaskDeadline tsk)
              A)
           (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
              Prosa_Implementation_Refinements_Task_Task
              Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
              Prosa_Implementation_Definitions_Task_TaskDeadline tsk_o))))
  (fun tsk_o : Prosa_Implementation_Refinements_Task_Task =>
   HSub_hSub_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
     (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
     (Prosa_Model_Task_Concept_TaskCost_task_cost_inst1 Prosa_Implementation_Refinements_Task_Task
        Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
        Prosa_Implementation_Definitions_Task_TaskCost tsk_o)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat

Arguments Prosa_Implementation_Refinements_EDF_FastSearchSpace_blocking_bound_NP ts tsk n%_Nat_scope
```
