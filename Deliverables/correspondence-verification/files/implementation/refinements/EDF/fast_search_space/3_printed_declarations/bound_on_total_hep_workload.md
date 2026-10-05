# `bound_on_total_hep_workload`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.fast_search_space.bound_on_total_hep_workload`
- Lean: `Prosa.Implementation.Refinements.EDF.FastSearchSpace.bound_on_total_hep_workload`
- Certificate: `bound_on_total_hep_workload_correspondence`

## Official Rocq

```coq
bound_on_total_hep_workload : seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat -> nat

bound_on_total_hep_workload is not universe polymorphic
Arguments bound_on_total_hep_workload ts%_seq_scope tsk (A Δ)%_nat_scope
bound_on_total_hep_workload is transparent
Expands to: Constant prosa.implementation.refinements.EDF.fast_search_space.bound_on_total_hep_workload
Declared in library prosa.implementation.refinements.EDF.fast_search_space, line 6, characters 11-38
bound_on_total_hep_workload
     : seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat -> nat
```

Body:

```coq
bound_on_total_hep_workload =
fun (ts : seq (Equality.sort task.Task)) (tsk : Equality.sort task.Task) (A Δ : nat) =>
\sum_(tsk_o <- ts | tsk_o != tsk) task_rbf tsk_o (minn (A + 1 + task_deadline tsk - task_deadline tsk_o) Δ)
     : seq (Equality.sort task.Task) -> Equality.sort task.Task -> nat -> nat -> nat

Arguments bound_on_total_hep_workload ts%_seq_scope tsk (A Δ)%_nat_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.FastSearchSpace.bound_on_total_hep_workload : List
    Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → ℕ → ℕ → ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.FastSearchSpace.bound_on_total_hep_workload : List
    Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.Task → ℕ → ℕ → ℕ :=
fun ts tsk A Δ =>
  Prosa.Util.Sum.sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk)) fun tsk_o =>
    Prosa.Implementation.Refinements.ArrivalCurve.task_rbf tsk_o
      (min (A + 1 + Prosa.Model.Task.Concept.task_deadline tsk - Prosa.Model.Task.Concept.task_deadline tsk_o) Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_bound_on_total_hep_workload
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat -> Nat
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_bound_on_total_hep_workload@{} =
fun (ts : List_inst1 Prosa_Implementation_Refinements_Task_Task)
  (tsk : Prosa_Implementation_Refinements_Task_Task) (A _UU0394_ : Nat) =>
Prosa_Util_Sum_sumFiltered_inst1 Prosa_Implementation_Refinements_Task_Task ts
  (fun tsk_o : Prosa_Implementation_Refinements_Task_Task =>
   Decidable_decide (Ne Prosa_Implementation_Refinements_Task_Task tsk_o tsk)
     (instDecidableNot (@eq Prosa_Implementation_Refinements_Task_Task tsk_o tsk)
        (Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task tsk_o tsk)))
  (fun tsk_o : Prosa_Implementation_Refinements_Task_Task =>
   Prosa_Implementation_Refinements_ArrivalCurve_task_rbf tsk_o
     (Min_min_inst1 Prosa_Behavior_Time_duration instMinNat
        (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
           (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) A
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
              (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
                 Prosa_Implementation_Refinements_Task_Task
                 Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                 Prosa_Implementation_Definitions_Task_TaskDeadline tsk))
           (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
              Prosa_Implementation_Refinements_Task_Task
              Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
              Prosa_Implementation_Definitions_Task_TaskDeadline tsk_o))
        _UU0394_))
     : List_inst1 Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_Task -> Nat -> Nat -> Nat

Arguments Prosa_Implementation_Refinements_EDF_FastSearchSpace_bound_on_total_hep_workload 
  ts tsk (x n)%_Nat_scope
```
