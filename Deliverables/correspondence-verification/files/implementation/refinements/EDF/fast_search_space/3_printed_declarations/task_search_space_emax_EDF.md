# `task_search_space_emax_EDF`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF`
- Lean: `Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF`
- Certificate: `task_search_space_emax_EDF_correspondence`

## Official Rocq

```coq
task_search_space_emax_EDF : Equality.sort Task -> Equality.sort Task -> nat -> seq nat

task_search_space_emax_EDF is not universe polymorphic
Arguments task_search_space_emax_EDF tsk tsko L%_nat_scope
task_search_space_emax_EDF is transparent
Expands to: Constant prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF
Declared in library prosa.implementation.refinements.EDF.fast_search_space, line 72, characters 13-39
task_search_space_emax_EDF
     : Equality.sort Task -> Equality.sort Task -> nat -> seq nat
```

Body:

```coq
task_search_space_emax_EDF =
fun (tsk tsko : Equality.sort Task) (L : nat) =>
let h := get_horizon_of_task tsko in
task_search_space_emax_EDF_h tsk tsko 0 ((L + (task_deadline tsk - task_deadline tsko)) %/ h).+1
     : Equality.sort Task -> Equality.sort Task -> nat -> seq nat

Arguments task_search_space_emax_EDF tsk tsko L%_nat_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF : Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task → ℕ → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF : Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task → ℕ → List ℕ :=
fun tsk tsko L =>
  have h := Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsko;
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF_h tsk tsko 0
    ((L + (Prosa.Model.Task.Concept.task_deadline tsk - Prosa.Model.Task.Concept.task_deadline tsko)) / h + 1)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF
     : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF@{} =
fun (tsk tsko : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task) (L : Nat) =>
let h := Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsko in
Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF_h tsk tsko
  (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
     (HDiv_hDiv_inst7 Nat Prosa_Behavior_Time_duration Nat (instHDiv_inst1 Nat Nat_instDiv)
        (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat) L
           (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
              Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
              (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
                 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
                 Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                 Prosa_Implementation_Definitions_Task_TaskDeadline tsk)
              (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
                 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
                 Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                 Prosa_Implementation_Definitions_Task_TaskDeadline tsko)))
        h)
     (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
     : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task -> Nat -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF 
  tsk tsko s%_Nat_scope
```
