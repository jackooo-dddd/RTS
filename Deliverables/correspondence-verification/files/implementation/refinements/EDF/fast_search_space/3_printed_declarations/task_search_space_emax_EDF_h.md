# `task_search_space_emax_EDF_h`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF_h`
- Lean: `Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF_h`
- Certificate: `task_search_space_emax_EDF_h_correspondence`

## Official Rocq

```coq
task_search_space_emax_EDF_h : Equality.sort Task -> Equality.sort Task -> nat -> nat -> seq nat

task_search_space_emax_EDF_h is not universe polymorphic
Arguments task_search_space_emax_EDF_h tsk tsko (l r)%_nat_scope
task_search_space_emax_EDF_h is transparent
Expands to: Constant prosa.implementation.refinements.EDF.fast_search_space.task_search_space_emax_EDF_h
Declared in library prosa.implementation.refinements.EDF.fast_search_space, line 63, characters 13-41
task_search_space_emax_EDF_h
     : Equality.sort Task -> Equality.sort Task -> nat -> nat -> seq nat
```

Body:

```coq
task_search_space_emax_EDF_h =
fun (tsk tsko : Equality.sort Task) (l r : nat) =>
let h := get_horizon_of_task tsko in
let offsets := [seq h * i | i <- iota l r] in
let emax_offsets := repeat_steps_with_offset tsko offsets in
let emax_edf_offsets :=
  shift_points_neg (shift_points_pos emax_offsets (task_deadline tsko)) (task_deadline tsk) in
     : Equality.sort Task -> Equality.sort Task -> nat -> nat -> seq nat

Arguments task_search_space_emax_EDF_h tsk tsko (l r)%_nat_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF_h : Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task → ℕ → ℕ → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF_h : Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task → ℕ → ℕ → List ℕ :=
fun tsk tsko l r =>
  have h := Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsko;
  have offsets := List.map (fun i => h * i) (List.range' l r);
  have emax_offsets := Prosa.Implementation.Refinements.ArrivalCurve.repeat_steps_with_offset tsko offsets;
  have emax_edf_offsets :=
    Prosa.Util.List.shift_points_neg
      (Prosa.Util.List.shift_points_pos emax_offsets (Prosa.Model.Task.Concept.task_deadline tsko))
      (Prosa.Model.Task.Concept.task_deadline tsk);
  List.map Nat.pred emax_edf_offsets
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF_h
     : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task -> Nat -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF_h@{} =
fun (tsk tsko : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task) (l r : Nat) =>
let h := Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsko in
let offsets :=
  List_map_inst3 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
    (fun x : Prosa_Behavior_Time_duration =>
     HMul_hMul_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
       (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat) h x)
    (List_range' l r (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
  in
let emax_offsets := Prosa_Implementation_Refinements_ArrivalCurve_repeat_steps_with_offset tsko offsets in
let emax_edf_offsets :=
  Prosa_Util_List_shift_points_neg
    (Prosa_Util_List_shift_points_pos emax_offsets
       (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
          Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
          Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
          Prosa_Implementation_Definitions_Task_TaskDeadline tsko))
    (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
       Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
       Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
       Prosa_Implementation_Definitions_Task_TaskDeadline tsk)
  in
List_map_inst3 Nat Nat Nat_pred emax_edf_offsets
     : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task -> Nat -> Nat -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF_h 
  tsk tsk (x____at___Init_Data_List_Basic527151790__hygCtx__hyg14 s)%_Nat_scope
```
